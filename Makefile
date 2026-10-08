PYTHON ?= python3

.PHONY: verify
verify:
	$(PYTHON) scripts/verify_all.py
