clean:
	rm -rf doc/
	rm -rf target/
	find . \( -name '*.a' -or \
		-name '*.o' -or \
		-name '*.so' -or \
		-name 'mlock' -or \
		-name '*~' \) \
		-print -exec rm {} \;
