{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

{-|

Translate a @ClassDecl@ (see "AST") to its @CCode@ (see "CCode.Main")
equivalent.

-}

module CodeGen.ClassDecl () where

import CodeGen.Typeclasses
import CodeGen.CCodeNames
import CodeGen.MethodDecl
import CodeGen.ClassTable
import CodeGen.Type
import CodeGen.Trace
import CodeGen.GC

import CCode.Main
import CCode.PrettyCCode ()

import Data.List
import Text.Printf (printf)

import qualified AST.AST as A
import qualified Identifiers as ID
import qualified Types as Ty

instance Translatable A.ClassDecl (ClassTable -> CCode FIN) where
  translate cdecl ctable
      | A.isActive cdecl = translateActiveClass cdecl ctable
      | A.isShared cdecl = translateSharedClass cdecl ctable
      | otherwise        = translatePassiveClass cdecl ctable

-- | Translates an active class into its C representation. Note
-- that there are additional declarations in the file generated by
-- "CodeGen.Header"
translateActiveClass cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) ctable =
    Program $ Concat $
      (LocalInclude "header.h") :
      [traitMethodSelector ctable cdecl] ++
      [typeStructDecl cdecl] ++
      [runtimeTypeInitFunDecl cdecl] ++
      [tracefunDecl cdecl] ++
      [constructorImpl Active cname ctable] ++
      methodImpls ++
      (map (methodImplWithFuture cname) nonStreamMethods) ++
      (map (methodImplOneWay cname) nonStreamMethods) ++
      (map (methodImplStream cname) streamMethods) ++
      [dispatchFunDecl cdecl] ++
      [runtimeTypeDecl cname]
    where
      methodImpls = map methodImpl cmethods
        where
          methodImpl mdecl = translate mdecl cdecl ctable
      (streamMethods, nonStreamMethods) = partition A.isStreamMethod cmethods

typeStructDecl :: A.ClassDecl -> CCode Toplevel
typeStructDecl cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) =
    let typeParams = Ty.getTypeParameters cname in
    StructDecl (AsType $ classTypeName cname) $
               ((encoreActorT, Var "_enc__actor") :
                (map (\ty -> (Ptr ponyTypeT, AsLval $ typeVarRefName ty)) typeParams ++
                   zip
                   (map (translate  . A.ftype) cfields)
                   (map (AsLval . fieldName . A.fname) cfields)))

dispatchFunDecl :: A.ClassDecl -> CCode Toplevel
dispatchFunDecl cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) =
    (Function (Static void) (classDispatchName cname)
     ([(Ptr encoreCtxT, encoreCtxVar),
       (Ptr ponyActorT, Var "_a"),
       (Ptr ponyMsgT, Var "_m")])
     (Seq [Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
                  (Cast (Ptr . AsType $ classTypeName cname) (Var "_a")),
           (Switch (Var "_m" `Arrow` Nam "id")
            (
             taskDispatchClause :
             (if (A.isMainClass cdecl)
              then ponyMainClause :
                   (methodClauses $ filter ((/= ID.Name "main") . A.methodName) cmethods)
              else methodClauses $ cmethods
             ))
            (Statement $ Call (Nam "printf") [String "error, got invalid id: %zd", AsExpr $ (Var "_m") `Arrow` (Nam "id")]))]))
     where
       ponyMainClause =
           (Nam "_ENC__MSG_MAIN",
            Seq $ [Assign (Decl (Ptr ponyMainMsgT, Var "msg")) (Cast (Ptr ponyMainMsgT) (Var "_m")),
                   Statement $ Call ((methodImplName Ty.mainType (ID.Name "main")))
                                    [AsExpr encoreCtxVar,
                                     (Cast (Ptr encActiveMainT) (Var "_a")),
                                     Call (Nam "_init_argv")
                                          [AsExpr encoreCtxVar,
                                           AsExpr $ (Var "msg") `Arrow` (Nam "argc"),
                                           AsExpr $ (Var "msg") `Arrow` (Nam "argv")]]])

       methodClauses = concatMap methodClause

       methodClause m = (mthdDispatchClause m) :
                         if not (A.isStreamMethod m)
                         then [oneWaySendDispatchClause m]
                         else []

       -- explode _enc__Foo_bar_msg_t struct into variable names
       methodUnpackArguments :: A.MethodDecl -> CCode Ty -> [CCode Stat]
       methodUnpackArguments mdecl msgTypeName =
         zipWith unpack (A.methodParams mdecl) [1..]
           where
             unpack :: A.ParamDecl -> Int -> CCode Stat
             unpack A.Param{A.pname, A.ptype} n = (Assign (Decl (translate ptype, (AsLval . argName $ pname))) ((Cast (msgTypeName) (Var "_m")) `Arrow` (Nam $ "f"++show n)))

       includeCtx xs = encoreCtxVar : xs

       -- TODO: pack in encore_arg_t the task, infering its type
       taskDispatchClause :: (CCode Name, CCode Stat)
       taskDispatchClause =
         let tmp = Var "task_tmp"
             taskRunnerStmt = Statement $ Call taskRunner [Var "_task"]
             decl = Assign (Decl (encoreArgT, tmp)) taskRunnerStmt
             futureFulfilStmt = Statement $ Call futureFulfil
                              [AsExpr encoreCtxVar,AsExpr $ Var "_fut", AsExpr tmp]
             taskFreeStmt = Statement $ Call taskFree [AsExpr $ Var "_task"]
             traceFuture = Statement $ Call ponyTraceObject (includeCtx [Var "_fut", futureTypeRecName `Dot` Nam "trace"])
             traceTask = Statement $ Call ponyTraceObject (includeCtx [Var "_task", AsLval $ Nam "NULL"])
         in
         (taskMsgId, Seq $ [unpackFuture, unpackTask, decl] ++
                             [Embed $ "",
                              Embed $ "// --- GC on receiving ----------------------------------------",
                              Statement $ Call (Nam "pony_gc_recv") ([encoreCtxVar]),
                              traceFuture,
                              traceTask,
                              Embed $ "//---You need to trace the task env and task dependencies---",
                              Statement $ Call (Nam "pony_recv_done") ([encoreCtxVar]),
                              Embed $ "// --- GC on sending ----------------------------------------",
                              Embed $ ""]++
                       [futureFulfilStmt, taskFreeStmt])

       mthdDispatchClause mdecl
           | A.isStreamMethod mdecl =
               (futMsgId cname mName,
                Seq $ unpackFuture : args ++
                      gcRecieve ++ [streamMethodCall])
           | otherwise =
               (futMsgId cname mName,
                Seq $ unpackFuture : args ++
                      gcRecieve ++ [methodCall])
           where
             args =
                 methodUnpackArguments mdecl
                 (Ptr . AsType $ futMsgTypeName cname mName)
             gcRecieve  =
                 gcRecv mParams
                 (Statement $ Call ponyTraceObject
                                   (includeCtx
                                      [Var "_fut",
                                       futureTypeRecName `Dot` Nam "trace"]))
             streamMethodCall =
                 Statement $ Call (methodImplName cname mName)
                                  (encoreCtxVar :
                                   Var "_this" :
                                   Var "_fut" :
                                   map (AsLval . argName . A.pname) mParams)
             methodCall =
                 Statement $
                   Call futureFulfil
                        [AsExpr encoreCtxVar,
                         AsExpr $ Var "_fut",
                         asEncoreArgT (translate mType)
                         (Call (methodImplName cname mName)
                               (encoreCtxVar : Var "_this" :
                                map (AsLval . argName . A.pname) mParams))]
             mName   = A.methodName mdecl
             mParams = A.methodParams mdecl
             mType   = A.methodType mdecl

       oneWaySendDispatchClause mdecl =
           (oneWayMsgId cname mName,
            Seq $ args ++ gcRecieve ++ [methodCall])
           where
             args =
                 methodUnpackArguments mdecl
                 (Ptr . AsType $ oneWayMsgTypeName cname mName)
             gcRecieve =
                 gcRecv mParams
                 (Comm "Not tracing the future in a oneWay send")
             methodCall =
                 Statement $
                   Call (methodImplName cname mName)
                        (encoreCtxVar : Var "_this" : map (AsLval . argName . A.pname) mParams)
             mName   = A.methodName mdecl
             mParams = A.methodParams mdecl

       unpackFuture =
         let
           lval = Decl (future, Var "_fut")
           rval = (Cast (Ptr $ encMsgT) (Var "_m")) `Arrow` (Nam "_fut")
         in
           Assign lval rval

       unpackTask =
         let
           lval = Decl (task, Var "_task")
           rval = (Cast (Ptr taskMsgT) (Var "_m")) `Arrow` (Nam "_task")
         in
           Assign lval rval

sendFutMsg :: Ty.Type -> ID.Name -> [CCode Name] -> [CCode Stat]
sendFutMsg cname mname args =
  let
    msgId = futMsgId cname mname
    msgTypeName = futMsgTypeName cname mname
    fields = [Nam $ "f" ++ show i | i <- [1..length args]]
    argPairs = zip fields args ++ [(Nam "_fut", Nam "_fut")]
  in
    sendMsg cname mname msgId msgTypeName argPairs

sendOneWayMsg :: Ty.Type -> ID.Name -> [CCode Name] -> [CCode Stat]
sendOneWayMsg cname mname args =
  let
    msgId = oneWayMsgId cname mname
    msgTypeName = oneWayMsgTypeName cname mname
    fields = [Nam $ "f" ++ show i | i <- [1..length args]]
    argPairs = zip fields args
  in
    sendMsg cname mname msgId msgTypeName argPairs

sendStreamMsg :: Ty.Type -> ID.Name -> [CCode Name] -> [CCode Stat]
sendStreamMsg cname mname args =
  let
    msgId = futMsgId cname mname
    msgTypeName = futMsgTypeName cname mname
    fields = [Nam $ "f" ++ show i | i <- [1..length args]]
    argPairs = zip fields args ++ [(Nam "_fut", Nam "_stream")]
  in
    sendMsg cname mname msgId msgTypeName argPairs

sendMsg :: Ty.Type -> ID.Name -> CCode Name -> CCode Name
  -> [(CCode Name, CCode Name)]
  -> [CCode Stat]
sendMsg cname mname msgId msgTypeName argPairs = [
  assignMsg
  , initMsg
  , sendMsg
  ]
  where
    thisName = "_this"
    msgType = AsType msgTypeName
    msgTypePtr = Ptr msgType
    msgName = "msg"
    declMsg = Decl (msgTypePtr, Var msgName)
    msgIdExpr = AsExpr. AsLval $ msgId
    msgSizeIndex = Call poolIndexName [Sizeof msgType]
    allocMsg = Call ponyAllocMsgName [msgSizeIndex, msgIdExpr]
    castAllocMsg = Cast msgTypePtr allocMsg
    assignMsg = Assign declMsg castAllocMsg

    assignMsgFields =
      [Assign (Var msgName `Arrow` f) rhs | (f,rhs) <- argPairs]
    initMsg = Seq assignMsgFields

    target = Cast (Ptr ponyActorT) $ Var thisName
    msgArg = Cast (Ptr ponyMsgT) $ Var msgName
    sendMsg = Statement $
      Call ponySendvName [AsExpr encoreCtxVar, target, msgArg]

initEncoreCtx :: CCode Stat
initEncoreCtx =
  Assign
    -- If we decide not to pass extra ctx around
    -- (Decl (Ptr encoreCtxT, AsLval encoreCtxName)) $
    encoreCtxName $
      Call (Nam "encore_ctx") ([] :: [CCode Lval])

methodImplWithFuture :: Ty.Type -> A.MethodDecl -> CCode Toplevel
methodImplWithFuture cname m =
  let
    retType = future
    fName = methodImplFutureName cname mName
    args = (Ptr encoreCtxT, encoreCtxVar) : this : zip argTypes argNames
    fBody = Seq $ [initEncoreCtx] ++
      [assignFut] ++
      ponyGcSendFuture argPairs ++
      msg ++
      [retStmt]
  in
    Function retType fName args fBody
  where
    thisName = "_this"
    mName = A.methodName m
    mParams = A.methodParams m
    mType = A.methodType m
    argNames = map (AsLval . argName . A.pname) mParams
    argTypes = map (translate . A.ptype) mParams
    this = (Ptr . AsType $ classTypeName cname, Var thisName)
    futVar = Var "_fut"
    declFut = Decl (future, futVar)
    futureMk mtype = Call futureMkFn [AsExpr encoreCtxVar, runtimeType mtype]
    assignFut = Assign declFut $ futureMk mType
    argPairs = zip (map A.ptype mParams) argNames
    msg = sendFutMsg cname mName $ map (argName . A.pname) mParams
    retStmt = Return futVar

methodImplOneWay :: Ty.Type -> A.MethodDecl -> CCode Toplevel
methodImplOneWay cname m =
  let
    retType = void
    fName = methodImplOneWayName cname mName
    args = (Ptr encoreCtxT, encoreCtxVar): this : zip argTypes argNames
    fBody = Seq $ [initEncoreCtx] ++
      ponyGcSendOneway argPairs ++
      msg
  in
    Function retType fName args fBody
  where
    thisName = "_this"
    mName = A.methodName m
    mParams = A.methodParams m
    mType = A.methodType m
    argNames = map (AsLval . argName . A.pname) mParams
    argTypes = map (translate . A.ptype) mParams
    this = (Ptr . AsType $ classTypeName cname, Var thisName)

    argPairs = zip (map A.ptype mParams) argNames
    msg = sendOneWayMsg cname mName $ map (argName . A.pname) mParams

methodImplStream :: Ty.Type -> A.MethodDecl -> CCode Toplevel
methodImplStream cname m =
  let
    retType = stream
    fName = methodImplStreamName cname mName
    args = (Ptr encoreCtxT, encoreCtxVar) : this : zip argTypes argNames
    fBody = Seq $ [initEncoreCtx] ++
      [assignFut] ++
      ponyGcSendStream argPairs ++
      msg ++
      [retStmt]
  in
    Function retType fName args fBody
  where
    thisName = "_this"
    mName = A.methodName m
    mParams = A.methodParams m
    mType = A.methodType m
    argNames = map (AsLval . argName . A.pname) mParams
    argTypes = map (translate . A.ptype) mParams
    this = (Ptr . AsType $ classTypeName cname, Var thisName)
    retVar = Var "_stream"
    declVar = Decl (stream, retVar)
    streamMk mtype = Call streamMkFn [encoreCtxVar]
    assignFut = Assign declVar $ streamMk mType
    argPairs = zip (map A.ptype mParams) argNames
    msg = sendStreamMsg cname mName $ map (argName . A.pname) mParams
    retStmt = Return retVar

ponyGcSendFuture :: [(Ty.Type, CCode Lval)] -> [CCode Stat]
ponyGcSendFuture argPairs =
  [Statement $ Call ponyGcSendName [encoreCtxVar]] ++
  (map (Statement . uncurry traceVariable) argPairs) ++
  [Statement . traceFuture $ Var "_fut"] ++
  [Statement $ Call ponySendDoneName [encoreCtxVar]]

ponyGcSendOneway :: [(Ty.Type, CCode Lval)] -> [CCode Stat]
ponyGcSendOneway argPairs =
  [Statement $ Call ponyGcSendName [encoreCtxVar]] ++
  (map (Statement . uncurry traceVariable) argPairs) ++
  [Comm "No tracing future for oneway msg"] ++
  [Statement $ Call ponySendDoneName [encoreCtxVar]]

ponyGcSendStream :: [(Ty.Type, CCode Lval)] -> [CCode Stat]
ponyGcSendStream argPairs =
  [Statement $ Call ponyGcSendName [encoreCtxVar]] ++
  (map (Statement . uncurry traceVariable) argPairs) ++
  [Statement . traceStream $ Var "_stream"] ++
  [Statement $ Call ponySendDoneName [encoreCtxVar]]

data Activity = Active | Shared | Passive

constructorImpl :: Activity -> Ty.Type -> ClassTable -> CCode Toplevel
constructorImpl act cname ctable =
  let
    retType = translate cname
    fName = constructorImplName cname
    args = [(Ptr encoreCtxT, encoreCtxVar)]
    fBody = Seq $
      [
      initEncoreCtx
      , assignThis
      ] ++
      decorateThis act ++
      [ret this]
  in
    Function retType fName args fBody
  where
    classType = AsType $ classTypeName cname
    thisType = Ptr classType
    cast = Cast thisType
    this = Var "this"
    declThis = Decl (thisType, this)
    runtimeType = Amp $ runtimeTypeName cname
    create = createCall act
    assignThis = Assign declThis $ cast create
    ret = Return

    createCall :: Activity -> CCode Expr
    createCall Active =
      Call encoreCreateName [AsExpr encoreCtxVar, runtimeType]
    createCall Shared =
      Call encoreCreateSoName [AsExpr encoreCtxVar, runtimeType]
    createCall Passive
      | is_subord cname ctable =
          Call encore_alloc_final_name
            [AsExpr encoreCtxVar, Sizeof classType,
             Cast (Ptr void) $ so_lockfree_subord_finalizer_name cname]
      | otherwise =
          Call encoreAllocName [AsExpr encoreCtxVar, Sizeof classType]

    decorateThis :: Activity -> [CCode Stat]
    decorateThis Passive = [Assign (this `Arrow` selfTypeField) runtimeType]
    decorateThis _ = []

prep_lf_entry :: String -> [CCode Stat]
prep_lf_entry thisName =
  [ init_to_trace thisName
  , call_on_entry
  ]
  where
    to_trace_t_ptr = Ptr to_trace_t
    to_trace_var = Var "_item"
    decl_to_trace = Decl (to_trace_t_ptr, to_trace_var)
    this = Cast (Ptr encoreSoT) $ Var thisName
    to_trace_new =
      Call to_trace_new_fn [this]
    init_to_trace thisName = Assign decl_to_trace to_trace_new
    call_on_entry =
      Statement $ Call so_lockfree_on_entry_fn [this, AsExpr to_trace_var]

prep_lf_exit :: String -> [CCode Stat]
prep_lf_exit thisName =
  map Statement [call_acc_recv, call_on_exit]
  where
    to_trace_var = Var "_item"
    this = Cast (Ptr encoreSoT) $ Var thisName
    call_acc_recv =
      Call so_lockfree_register_acc_to_recv_fn [encoreCtxVar, to_trace_var]
    call_on_exit =
      Call so_lockfree_on_exit_fn [this, AsExpr to_trace_var]

translateSharedClass cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) ctable =
  Program $ Concat $
    (LocalInclude "header.h") :
    [traitMethodSelector ctable cdecl] ++
    [typeStructDecl cdecl] ++
    [runtimeTypeInitFunDecl cdecl] ++
    [inverse_trace_fun_decls cdecl] ++
    [tracefunDecl cdecl] ++
    [constructorImpl Shared cname ctable] ++
    [class_non_spec_subord_fields_apply cdecl ctable] ++
    [class_subord_fields_final_apply cdecl ctable] ++
    methodImpls ++
    [so_method_impl_with_future strategy method | method <- cmethods, strategy <- strategies] ++
    (map (methodImplOneWay cname) cmethods) ++
    [dispatchFunDecl cdecl] ++
    [runtimeTypeDecl cname]
  where
    typeStructDecl :: A.ClassDecl -> CCode Toplevel
    typeStructDecl cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) =
        let typeParams = Ty.getTypeParameters cname in
        StructDecl (AsType $ classTypeName cname) $
                   ((encoreSoT, Var "_enc__so") :
                    (map (\ty -> (Ptr ponyTypeT, AsLval $ typeVarRefName ty)) typeParams ++
                       zip
                       (map (translate  . A.ftype) cfields)
                       (map (AsLval . fieldName . A.fname) cfields)))

    methodImpls = map methodDecl cmethods
      where
        methodDecl mdecl = translate mdecl cdecl ctable

    strategies = [
        -- ("SO_ACTOR", methodImplWithFuture)
      ("SO_LOCKFREE", method_future_so_lf)
      -- , ("SO_LOCKFREE", methodImplWithFuture)
      ]

    so_method_impl_with_future ::
      (String, Ty.Type -> A.MethodDecl -> CCode Toplevel)
        -> A.MethodDecl -> CCode Toplevel
    so_method_impl_with_future (macro, fun) = IfDefine macro . fun cname

    method_future_so_lf :: Ty.Type -> A.MethodDecl -> CCode Toplevel
    method_future_so_lf cname m =
      let
        retType = future
        fName = methodImplFutureName cname mName
        args = (Ptr encoreCtxT, encoreCtxVar) : this : zip argTypes argNames
        fBody = Seq $ [initEncoreCtx] ++
          [assignFut] ++
          prep_lf_entry thisName ++
          [fulfil_fut] ++
          prep_lf_exit thisName ++
          [retStmt]
      in
        Function retType fName args fBody
      where
        thisName = "_this"
        mName = A.methodName m
        mParams = A.methodParams m
        mType = A.methodType m
        argNames = map (AsLval . argName . A.pname) mParams
        argTypes = map (translate . A.ptype) mParams
        this = (Ptr . AsType $ classTypeName cname, Var thisName)
        futVar = Var "_fut"
        declFut = Decl (future, futVar)
        call_actual_method =
          asEncoreArgT (translate mType)
          (Call (methodImplName cname mName)
                (encoreCtxVar : Var thisName :
                 map (AsLval . argName . A.pname) mParams))
        futureMk mtype =
          Call futureMkFn [AsExpr encoreCtxVar, runtimeType mtype]
        -- futureMk mtype =
        --   Call futureFulfilledMkFn
        --     [AsExpr encoreCtxVar, runtimeType mtype, call_actual_method]
        assignFut = Assign declFut $ futureMk mType
        argPairs = zip (map A.ptype mParams) argNames
        trace_args argPairs =
          [Statement $ Call ponyGcSendName [encoreCtxVar]] ++
          (map (Statement . uncurry traceVariable) argPairs) ++
          [Statement $ Call ponySendDoneName [encoreCtxVar]]
        fulfil_fut =
          Statement $
           Call futureFulfil
             [AsExpr encoreCtxVar,
              AsExpr futVar,
              asEncoreArgT (translate mType)
              (Call (methodImplName cname mName)
                    (encoreCtxVar : Var thisName :
                     map (AsLval . argName . A.pname) mParams))]
        retStmt = Return futVar

    runtimeTypeDecl cname =
      AssignTL
       (Decl (Typ "pony_type_t", AsLval $ runtimeTypeName cname)) $
          DesignatedInitializer $ [ (Nam "id", AsExpr . AsLval $ classId cname)
          , (Nam "size", Call (Nam "sizeof") [AsLval $ classTypeName cname])
          , (Nam "trace", AsExpr . AsLval $ (classTraceFnName cname))
          , (Nam "dispatch", AsExpr . AsLval $ (classDispatchName cname))
          , (Nam "final", AsExpr . AsLval $ (encore_so_finalizer))
          , (Nam "vtable", AsExpr . AsLval $ traitMethodSelectorName)
          ]

-- | Translates a passive class into its C representation. Note
-- that there are additional declarations (including the data
-- struct for instance variables) in the file generated by
-- "CodeGen.Header"
translatePassiveClass cdecl@(A.Class{A.cname, A.cfields, A.cmethods}) ctable =
  Program $ Concat $
    (LocalInclude "header.h") :
    [traitMethodSelector ctable cdecl] ++
    [runtimeTypeInitFunDecl cdecl] ++
    [so_lockfree_subord_finalizer cdecl ctable] ++
    [inverse_trace_fun_decls cdecl] ++
    [tracefunDecl cdecl] ++
    [constructorImpl Passive cname ctable] ++
    methodImpls ++
    [dispatchfunDecl] ++
    [runtimeTypeDecl cname]
  where
    methodImpls = map methodDecl cmethods
        where
          methodDecl mdecl = translate mdecl cdecl ctable
    dispatchfunDecl =
      Function (Static void) (classDispatchName cname)
               ([(Ptr encoreCtxT, encoreCtxVar),
                 (Ptr ponyActorT, Var "_a"),
                 (Ptr ponyMsgT, Var "_m")])
               (Comm "Stub! Might be used when we have dynamic dispatch on passive classes")

traitMethodSelector :: ClassTable -> A.ClassDecl -> CCode Toplevel
traitMethodSelector ctable A.Class{A.cname, A.ccapability} =
  let
    retType = Static (Ptr void)
    fname = traitMethodSelectorName
    args = [(Typ "int" , Var "id")]
    cond = Var "id"
    traitTypes = Ty.typesFromCapability ccapability
    traitMethods = map (`lookupMethods` ctable) traitTypes
    cases = concat $ zipWith (traitCase cname) traitTypes traitMethods
    err = String "error, got invalid id: %d"
    defaultCase = Statement $ Call (Nam "printf") [err, AsExpr $ Var "id"]
    switch = Switch cond cases defaultCase
    body = Seq [ switch, Return Null ]
  in
    Function retType fname args body
  where
    traitCase :: Ty.Type -> Ty.Type -> [A.FunctionHeader] ->
                 [(CCode Name, CCode Stat)]
    traitCase cname tname tmethods =
        let
            methodNames = map A.hname tmethods
            caseNames   = map (msgId tname) methodNames
            caseStmts   = map (Return . methodImplName cname) methodNames
        in
          zip caseNames caseStmts

runtimeTypeInitFunDecl :: A.ClassDecl -> CCode Toplevel
runtimeTypeInitFunDecl A.Class{A.cname, A.cfields, A.cmethods} =
    Function void (runtimeTypeInitFnName cname)
                 [(Ptr . AsType $ classTypeName cname, Var "this"), (Embed "...", Embed "")]
                   (Seq $
                    (Statement $ Decl (Typ "va_list", Var "params")) :
                    (Statement $ Call (Nam "va_start") [Var "params", Var "this"]) :
                    map initRuntimeType typeParams ++
                    [Statement $ Call (Nam "va_end") [Var "params"]])
        where
          typeParams = Ty.getTypeParameters cname
          initRuntimeType ty =
              Assign (Var "this" `Arrow` typeVarRefName ty)
                     (Call (Nam "va_arg") [Var "params", Var "pony_type_t *"])

so_lockfree_subord_finalizer :: A.ClassDecl -> ClassTable -> CCode Toplevel
so_lockfree_subord_finalizer A.Class{A.cname, A.cfields, A.cmethods} ctable =
  Function void (so_lockfree_subord_finalizer_name cname)
    [(Ptr void, Var "p")]
    (Seq $
      [ Statement $ If (Call (Nam "so_lockfree_is_published") [Var "p"])
          Skip $ Return $ Var ""
      , Assign (Decl (Ptr encoreCtxT, AsLval encoreCtxName)) $
         Call (Nam "encore_ctx") ([] :: [CCode Lval])
      , Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
         (Var "p")
      ] ++
      map traceField cfields)
  where
    traceField A.Field {A.fmods, A.ftype, A.fname}
      | is_subord ftype ctable =
          Statement $ Call lf_so_passive_final_name
            [encoreCtxVar, Var "_this" `Arrow` fieldName fname]
      | otherwise =
          Comm $ printf "Skipping %s %s fields" (show fname) (show fmods)

is_subord t ctable =
  Ty.isClassType t &&
    (any Ty.isSpineRefType $
      Ty.typesFromCapability $ lookup_implemented_capa t ctable)

class_non_spec_subord_fields_apply :: A.ClassDecl -> ClassTable
  -> CCode Toplevel
class_non_spec_subord_fields_apply A.Class{A.cname, A.cfields} ctable =
  Function void (class_non_spec_subord_fields_apply_name cname)
    [(Ptr void, Var "p")]
    (Seq $
     (Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
             (Var "p")) :
      map traceField cfields)
  where
    black_list = [A.Spec, A.Once]

    traceField A.Field {A.fmods, A.ftype, A.fname}
      | null (fmods `intersect` black_list) && is_subord ftype ctable =
          let var = Var . show $ fieldName fname
              field = Var "_this" `Arrow` fieldName fname
              fieldAssign = Assign (Decl (translate ftype, var)) field
          in Seq [ fieldAssign
                 , Statement $ Call
                     (Nam "so_lockfree_non_spec_subord_field_apply") [field]]
      | otherwise =
          Comm $ printf "Skipping %s %s fields" (show fname) (show fmods)

class_subord_fields_final_apply :: A.ClassDecl -> ClassTable
  -> CCode Toplevel
class_subord_fields_final_apply A.Class{A.cname, A.cfields} ctable =
  Function void (class_subord_fields_final_apply_name cname)
    [(Ptr encoreCtxT, encoreCtxVar), (Ptr void, Var "p")]
    (Seq $
     (Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
             (Var "p")) :
      map traceField cfields)
  where
    traceField A.Field {A.fmods, A.ftype, A.fname}
      | is_subord ftype ctable =
          let var = Var . show $ fieldName fname
              field = Var "_this" `Arrow` fieldName fname
              fieldAssign = Assign (Decl (translate ftype, var)) field
          in Seq [ fieldAssign
                 , Statement $
                     Call (Nam "so_lockfree_subord_field_final_apply")
                       [encoreCtxVar, field]]
      | otherwise =
          Comm $ printf "Skipping %s %s fields" (show fname) (show fmods)

inverse_trace_fun_decls :: A.ClassDecl -> CCode Toplevel
inverse_trace_fun_decls A.Class{A.cname, A.cfields, A.cmethods} =
  Concat $
    [Function void (class_inverse_trace_fn_name cname)
           [(Ptr encoreCtxT, encoreCtxVar), (Ptr void, Var "p")]
           (Seq $
            (Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
                    (Var "p")) :
             map traceField cfields)
    ] ++
    [Function void (class_inverse_field_trace_fn_name cname $ A.fname field)
           [(Ptr encoreCtxT, encoreCtxVar), (Ptr void, Var "p")]
           (Seq $
            (Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
                    (Var "p")) :
             map traceField (cfields \\ [field]))
    | field <- cfields]
  where
    white_list = [A.Spec, A.Once]

    traceField A.Field {A.fmods, A.ftype, A.fname}
      | null $ fmods `intersect` white_list =
          Comm $ printf "Skipping %s %s fields" (show fname) (show fmods)
      | otherwise =
        let var = Var . show $ fieldName fname
            field = Var "_this" `Arrow` fieldName fname
            fieldAssign = Assign (Decl (translate ftype, var)) field
        in Seq [fieldAssign, inverse_trace_variable ftype var]

tracefunDecl :: A.ClassDecl -> CCode Toplevel
tracefunDecl A.Class{A.cname, A.cfields, A.cmethods} =
    case find ((== Ty.getId cname ++ "_trace") . show . A.methodName) cmethods of
      Just mdecl@(A.Method{A.mbody}) ->
          Function void (classTraceFnName cname)
                   [(Ptr encoreCtxT, encoreCtxVar), (Ptr void, Var "p")]
                   (Statement $ Call (methodImplName cname (A.methodName mdecl))
                                [encoreCtxVar, Var "p"])
      Nothing ->
          Function void (classTraceFnName cname)
                   [(Ptr encoreCtxT, encoreCtxVar),
                   (Ptr void, Var "p")]
                   (Seq $
                    Assign (Decl (Ptr . AsType $ classTypeName cname, Var "_this"))
                            (Var "p") :
                     map traceField cfields)
    where
      -- traceField fld@(A.Field {A.ftype, A.fname}) =
      --   let var = Var . show $ fieldName fname
      --       field = if A.isOnceField fld  || A.isSpecField fld
      --               then unfreeze ftype (Var "_this" `Arrow` fieldName fname)
      --               else AsExpr $ Var "_this" `Arrow` fieldName fname
      --       fieldAssign = Assign (Decl (translate ftype, var)) field
      --   in Seq [fieldAssign, traceVariable ftype var]
      skipping_list = [A.Spec, A.Once]

      traceField A.Field {A.fmods, A.ftype, A.fname}
        | not . null $ fmods `intersect` skipping_list =
            Comm $ printf "Skipping %s %s fields" (show fname) (show fmods)
        | otherwise =
          let var = Var . show $ fieldName fname
              field = Var "_this" `Arrow` fieldName fname
              fieldAssign = Assign (Decl (translate ftype, var)) field
          in Seq [fieldAssign, traceVariable ftype var]

runtimeTypeDecl cname =
  AssignTL
   (Decl (Typ "pony_type_t", AsLval $ runtimeTypeName cname)) $
      DesignatedInitializer $ [ (Nam "id", AsExpr . AsLval $ classId cname)
      , (Nam "size", Call (Nam "sizeof") [AsLval $ classTypeName cname])
      , (Nam "trace", AsExpr . AsLval $ (classTraceFnName cname))
      , (Nam "dispatch", AsExpr . AsLval $ (classDispatchName cname))
      , (Nam "vtable", AsExpr . AsLval $ traitMethodSelectorName)
      ]
