.PHONY: clean
clean:
	rm -rf *_src/
	find . -maxdepth 1 -executable -type f \
	  | egrep -v '.*\.(sh|enc)' | xargs -r rm
