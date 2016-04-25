{-# LANGUAGE FlexibleContexts #-}
{-|
Defines how things will be called in the CCode generated by CodeGen.hs
Provides mappings from class/method names to their C-name.

The purpose of this module is to

 - get one central place where identifiers in the generated code can be changed

 - ease following of good conventions (ie use @Ptr char@ instead of @Embed "char*"@)

-}

module CodeGen.CCodeNames where

import qualified Identifiers as ID
import Types as Ty
import CCode.Main
import Data.List
import Data.Char
import Data.String.Utils

import qualified AST.AST as A

import Text.Printf (printf)

char :: CCode Ty
char = Typ "char"

int :: CCode Ty
int = Typ "int64_t"

uint :: CCode Ty
uint = Typ "uint64_t"

bool :: CCode Ty
bool = Typ "int64_t" -- For pony argument tag compatibility. Should be changed to something smaller

double :: CCode Ty
double = Typ "double"

void :: CCode Ty
void = Typ "void"

encoreActorT :: CCode Ty
encoreActorT = Typ "encore_actor_t"

to_trace_t :: CCode Ty
to_trace_t = Typ "to_trace_t"

encoreSoT :: CCode Ty
encoreSoT = Typ "encore_so_t"

ponyTypeT :: CCode Ty
ponyTypeT = Typ "pony_type_t"

ponyActorT :: CCode Ty
ponyActorT = Typ "pony_actor_t"

ponyActorTypeT :: CCode Ty
ponyActorTypeT = Typ "pony_actor_type_t"

encoreArgT :: CCode Ty
encoreArgT = Typ "encore_arg_t"

isEncoreArgT :: CCode Ty -> Bool
isEncoreArgT (Typ "encore_arg_t") = True
isEncoreArgT _ = False

ponyMsgT :: CCode Ty
ponyMsgT = Typ "pony_msg_t"

ponyMainMsgName :: String
ponyMainMsgName = "pony_main_msg_t"

ponyMainMsgT :: CCode Ty
ponyMainMsgT = Typ ponyMainMsgName

encActiveMainName :: String
encActiveMainName = "_enc__active_Main_t"

encActiveMainT :: CCode Ty
encActiveMainT = Typ encActiveMainName

encMsgT :: CCode Ty
encMsgT = Typ "encore_fut_msg_t"

taskMsgT = Typ "encore_task_msg_s"

encOnewayMsgT :: CCode Ty
encOnewayMsgT = Typ "encore_oneway_msg_t"

closure :: CCode Ty
closure = Ptr $ Typ "closure_t"

task :: CCode Ty
task = Ptr $ Typ "encore_task_s"

future :: CCode Ty
future = Ptr $ Typ "future_t"

stream :: CCode Ty
stream = Ptr $ Typ "stream_t"

array :: CCode Ty
array = Ptr $ Typ "array_t"

tuple :: CCode Ty
tuple = Ptr $ Typ "tuple_t"

rangeT :: CCode Ty
rangeT = Typ "range_t"

range :: CCode Ty
range = Ptr rangeT

optionT :: CCode Name
optionT = Nam "option_t"

option :: CCode Ty
option = Ptr $ Typ "option_t"

par :: CCode Ty
par = Ptr $ Typ "par_t"

capability :: CCode Ty
capability = Ptr $ Typ "capability_t"

ponyTraceFnType :: CCode Ty
ponyTraceFnType = Typ "pony_trace_fn"

ponyTrace :: CCode Name
ponyTrace = Nam "pony_trace"

ponyTraceObject :: CCode Name
ponyTraceObject = Nam "pony_traceobject"

ponyTraceActor :: CCode Name
ponyTraceActor = Nam "pony_traceactor"

unit :: CCode Lval
unit = Embed "UNIT"

nothing :: CCode Lval
nothing = Var "NOTHING"

just :: CCode Lval
just = Var "JUST"

freeze :: UsableAs e Expr => Ty.Type -> CCode e -> CCode Expr
freeze ty e
    | Ty.isRefType ty = Call (Nam "FREEZE") [e]
    | otherwise = EmbedC e

unfreeze :: UsableAs e Expr => Ty.Type -> CCode e -> CCode Expr
unfreeze ty e
    | Ty.isRefType ty = Call (Nam "UNFREEZE") [e]
    | otherwise = EmbedC e

encoreName :: String -> String -> String
encoreName kind name =
  let
    (prefix, name') = fixPrimes name
    enc = let alphas = filter isAlpha kind
          in if not (null alphas) && all isUpper alphas
             then "_ENC_"
             else "_enc_"
    nonEmptys = filter (not . null) [enc, prefix, kind, name']
  in
    intercalate "_" nonEmptys

fixPrimes name
    | '\'' `elem` name =
        let nameWithoutPrimes = replace "'" "_" name
            expandedName = replace "'" "_prime" name
        in (nameWithoutPrimes, expandedName)
    | otherwise = ("", name)

selfTypeField :: CCode Name
selfTypeField = Nam $ encoreName "self_type" ""

-- | each method is implemented as a function with a `this`
-- pointer. This is the name of that function
methodImplName :: Ty.Type -> ID.Name -> CCode Name
methodImplName clazz mname = Nam $ methodImplNameStr clazz mname

methodImplFutureName :: Ty.Type -> ID.Name -> CCode Name
methodImplFutureName clazz mname =
  Nam $ methodImplFutureNameStr clazz mname

methodImplOneWayName :: Ty.Type -> ID.Name -> CCode Name
methodImplOneWayName clazz mname =
  Nam $ methodImplOneWayNameStr clazz mname

methodImplStreamName :: Ty.Type -> ID.Name -> CCode Name
methodImplStreamName clazz mname =
  Nam $ encoreName "method" $ printf "%s_%s_stream" (Ty.getId clazz) (show mname)

methodImplNameStr :: Ty.Type -> ID.Name -> String
methodImplNameStr clazz mname =
  encoreName "method" $ Ty.getId clazz ++ "_" ++ show mname

methodImplFutureNameStr :: Ty.Type -> ID.Name -> String
methodImplFutureNameStr clazz mname =
  methodImplNameStr clazz mname ++ "_future"

methodImplOneWayNameStr :: Ty.Type -> ID.Name -> String
methodImplOneWayNameStr clazz mname =
  methodImplNameStr clazz mname ++ "_one_way"

constructorImplName :: Ty.Type -> CCode Name
constructorImplName clazz = Nam $ encoreName "constructor" (Ty.getId clazz)

encoreCreateName :: CCode Name
encoreCreateName = Nam "encore_create"

encoreCreateSoName :: CCode Name
encoreCreateSoName = Nam "encore_create_so"

encoreAllocName :: CCode Name
encoreAllocName = Nam "encore_alloc"

partySequence :: CCode Name
partySequence = Nam "party_sequence"

partyJoin :: CCode Name
partyJoin = Nam "party_join"

partyExtract :: CCode Name
partyExtract = Nam "party_extract"

partyEach :: CCode Name
partyEach = Nam "party_each"

partyNewParP :: CCode Name
partyNewParP = Nam "new_par_p"

partyNewParV :: CCode Name
partyNewParV = Nam "new_par_v"

partyNewParF :: CCode Name
partyNewParF = Nam "new_par_f"

argName :: ID.Name -> CCode Name
argName name = Nam $ encoreName "arg" (show name)

fieldName :: ID.Name -> CCode Name
fieldName name =
    Nam $ encoreName "field" (show name)

globalClosureName :: ID.Name -> CCode Name
globalClosureName funname =
    Nam $ encoreName "closure" (show funname)

globalFunctionClosureNameOf :: A.Function -> CCode Name
globalFunctionClosureNameOf f = globalClosureName $ A.functionName f

globalFunctionName :: ID.Name -> CCode Name
globalFunctionName funname =
    Nam $ encoreName "global_fun" (show funname)

globalFunctionNameOf :: A.Function -> CCode Name
globalFunctionNameOf f = globalFunctionName $ A.functionName f

globalFunctionWrapperNameOf :: A.Function -> CCode Name
globalFunctionWrapperNameOf f =
  Nam $ encoreName "global_fun_wrapper" $ show $ A.functionName f

closureStructName :: CCode Name
closureStructName = Nam "closure"

closureStructFFieldName :: CCode Name
closureStructFFieldName = Nam "call"

closureFunName :: String -> CCode Name
closureFunName name =
    Nam $ encoreName "closure_fun" name

closureEnvName :: String -> CCode Name
closureEnvName name =
    Nam $ encoreName "env" name

closureTraceName :: String -> CCode Name
closureTraceName name =
    Nam $ encoreName "trace" name

taskFunctionName :: String -> CCode Name
taskFunctionName name =
    Nam $ encoreName "task" name

taskEnvName :: String -> CCode Name
taskEnvName name =
    Nam $ encoreName "task_env" name

taskDependencyName :: String -> CCode Name
taskDependencyName name =
    Nam $ encoreName "task_dep" name

taskTraceName :: String -> CCode Name
taskTraceName name =
    Nam $ encoreName "task_trace" name

streamHandle :: CCode Lval
streamHandle = Var "_stream"

typeVarRefName :: Ty.Type -> CCode Name
typeVarRefName ty =
    Nam $ encoreName "type" (show ty)

classId :: Ty.Type -> CCode Name
classId ty =
    Nam $ encoreName "ID" (Ty.getId ty)

refTypeId :: Ty.Type -> CCode Name
refTypeId ty =
    Nam $ encoreName "ID" (Ty.getId ty)

traitMethodSelectorName = Nam "trait_method_selector"

encore_so_finalizer = Nam "encore_so_finalinzer"

-- | each class, in C, provides a dispatch function that dispatches
-- messages to the right method calls. This is the name of that
-- function.
classDispatchName :: Ty.Type -> CCode Name
classDispatchName clazz =
    Nam $ encoreName "dispatch" (Ty.getId clazz)

classTraceFnName :: Ty.Type -> CCode Name
classTraceFnName clazz =
    Nam $ encoreName "trace" (Ty.getId clazz)

class_inverse_trace_fn_name :: Ty.Type -> CCode Name
class_inverse_trace_fn_name clazz =
    Nam $ encoreName "inverse_trace" $ Ty.getId clazz

class_inverse_field_trace_fn_name :: Ty.Type -> ID.Name -> CCode Name
class_inverse_field_trace_fn_name clazz field =
    Nam $ encoreName ("inverse_" ++ show field ++ "_trace") $ Ty.getId clazz

runtimeTypeInitFnName :: Ty.Type -> CCode Name
runtimeTypeInitFnName clazz =
    Nam $ encoreName "type_init" (Ty.getId clazz)

ponyAllocMsgName :: CCode Name
ponyAllocMsgName = Nam "pony_alloc_msg"

poolIndexName :: CCode Name
poolIndexName = Nam "POOL_INDEX"

futMsgTypeName :: Ty.Type -> ID.Name -> CCode Name
futMsgTypeName cls mname =
    Nam $ encoreName "fut_msg" (Ty.getId cls ++ "_" ++ show mname ++ "_t")

oneWayMsgTypeName :: Ty.Type -> ID.Name -> CCode Name
oneWayMsgTypeName cls mname =
    Nam $ encoreName "oneway_msg" (Ty.getId cls ++ "_" ++ show mname ++ "_t")

msgId :: Ty.Type -> ID.Name -> CCode Name
msgId ref mname =
    Nam $ encoreName "MSG" (Ty.getId ref ++ "_" ++ show mname)

futMsgId :: Ty.Type -> ID.Name -> CCode Name
futMsgId ref mname =
    Nam $ encoreName "FUT_MSG" (Ty.getId ref ++ "_" ++ show mname)

taskMsgId :: CCode Name
taskMsgId = Nam $ encoreName "MSG" "TASK"

oneWayMsgId :: Ty.Type -> ID.Name -> CCode Name
oneWayMsgId cls mname =
    Nam $ encoreName "ONEWAY_MSG" (Ty.getId cls ++ "_" ++ show mname)

typeNamePrefix :: Ty.Type -> String
typeNamePrefix ref
  | Ty.isActiveClassType ref = encoreName "active" id
  | Ty.isSharedClassType ref = encoreName "shared" id
  | Ty.isPassiveClassType ref = encoreName "passive" id
  | Ty.isTraitType ref = encoreName "trait" id
  | otherwise = error $ "type_name_prefix Type '" ++ show ref ++
                        "' isnt reference type!"
  where
    id = Ty.getId ref

ponySendvName :: CCode Name
ponySendvName = Nam "pony_sendv"

ponyGcSendName :: CCode Name
ponyGcSendName = Nam "pony_gc_send"

ponyGcRecvName :: CCode Name
ponyGcRecvName = Nam "pony_gc_recv"

ponyRecvDoneName :: CCode Name
ponyRecvDoneName = Nam "pony_recv_done"

ponySendDoneName :: CCode Name
ponySendDoneName = Nam "pony_send_done"

refTypeName :: Ty.Type -> CCode Name
refTypeName ref = Nam $ typeNamePrefix ref ++ "_t"

classTypeName :: Ty.Type -> CCode Name
classTypeName ref = Nam $ typeNamePrefix ref ++ "_t"

runtimeTypeName :: Ty.Type -> CCode Name
runtimeTypeName ref = Nam $ typeNamePrefix ref ++ "_type"

futureTraceFn :: CCode Name
futureTraceFn = Nam "future_trace"

futureFulfil :: CCode Name
futureFulfil = Nam "future_fulfil"

futureAwait :: CCode Name
futureAwait = Nam "future_await"

futureGetActor :: CCode Name
futureGetActor = Nam "future_get_actor"

futureChainActor :: CCode Name
futureChainActor = Nam "future_chain_actor"

actorSuspend :: CCode Name
actorSuspend = Nam "actor_suspend"

streamGet :: CCode Name
streamGet = Nam "stream_get"

streamPut :: CCode Name
streamPut = Nam "stream_put"

streamClose :: CCode Name
streamClose = Nam "stream_close"

streamGetNext :: CCode Name
streamGetNext = Nam "stream_get_next"

streamEos :: CCode Name
streamEos = Nam "stream_eos"

streamMkFn :: CCode Name
streamMkFn = Nam "stream_mk"

futureMkFn :: CCode Name
futureMkFn = Nam "future_mk"

futureFulfilledMkFn :: CCode Name
futureFulfilledMkFn = Nam "future_fulfilled_mk"

to_trace_new_fn :: CCode Name
to_trace_new_fn = Nam "so_to_trace_new"

so_lockfree_on_entry_fn :: CCode Name
so_lockfree_on_entry_fn = Nam "so_lockfree_on_entry"

so_lockfree_register_acc_to_recv_fn :: CCode Name
so_lockfree_register_acc_to_recv_fn = Nam "so_lockfree_register_acc_to_recv"

so_lockfree_on_exit_fn :: CCode Name
so_lockfree_on_exit_fn = Nam "so_lockfree_on_exit"

rangeMkFn :: CCode Name
rangeMkFn = Nam "range_mk"

taskMkFn :: CCode Name
taskMkFn = Nam "task_mk"

arrayMkFn :: CCode Name
arrayMkFn = Nam "array_mk"

tupleMkFn :: CCode Name
tupleMkFn = Nam "tuple_mk"

closureMkFn :: CCode Name
closureMkFn = Nam "closure_mk"

closureCallName :: CCode Name
closureCallName = Nam "closure_call"

optionMkFn :: CCode Name
optionMkFn = Nam "option_mk"

closureTraceFn :: CCode Name
closureTraceFn = Nam "closure_trace"

arrayTraceFn :: CCode Name
arrayTraceFn = Nam "array_trace"

optionTraceFn :: CCode Name
optionTraceFn = Nam "option_trace"

rangeTraceFn :: CCode Name
rangeTraceFn = Nam "range_trace"

streamTraceFn :: CCode Name
streamTraceFn = Nam "stream_trace"

futureTypeRecName :: CCode Name
futureTypeRecName = Nam $ "future_type"

closureTypeRecName :: CCode Name
closureTypeRecName = Nam $ "closure_type"

arrayTypeRecName :: CCode Name
arrayTypeRecName = Nam $ "array_type"

rangeTypeRecName :: CCode Name
rangeTypeRecName = Nam $ "range_type"

partyTypeRecName :: CCode Name
partyTypeRecName = Nam $ "party_type"

encoreCtxName :: CCode Name
encoreCtxName = Nam "_ctx"

encoreCtxT :: CCode Ty
encoreCtxT = Typ "pony_ctx_t"

encoreCtxVar :: CCode Lval
encoreCtxVar = Var "_ctx"

arrayGet :: CCode Name
arrayGet = Nam "array_get"

arraySet :: CCode Name
arraySet = Nam "array_set"

arraySize :: CCode Name
arraySize = Nam "array_size"

tupleSet :: CCode Name
tupleSet = Nam "tuple_set"

tupleGet :: CCode Name
tupleGet = Nam "tuple_get"

tupleSetType :: CCode Name
tupleSetType = Nam "tuple_set_type"

rangeStart :: CCode Name
rangeStart = Nam "range_start"

rangeStop :: CCode Name
rangeStop = Nam "range_stop"

rangeStep :: CCode Name
rangeStep = Nam "range_step"

rangeAssertStep :: CCode Name
rangeAssertStep = Nam "range_assert_step"

taskAttachFut :: CCode Name
taskAttachFut = Nam "task_attach_fut"

taskSchedule :: CCode Name
taskSchedule = Nam "task_schedule"

taskRunner :: CCode Name
taskRunner = Nam "task_runner"

taskFree :: CCode Name
taskFree = Nam "task_free"

optionTypeRecName :: CCode Name
optionTypeRecName = Nam "option_type"
