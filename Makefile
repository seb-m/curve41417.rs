doc:
	cargo doc --no-deps

clean:
	rm -rf doc/
	rm -rf target/
	find . \( -name '*.a' -or \
		-name '*.o' -or \
		-name '*.so' -or \
		-name 'mlock' -or \
		-name 'Cargo.lock' -or \
		-name '*~' \) \
		-print -exec rm {} \;
