#!/bin/bash

eflint-repl case_emergency.eflint --test-mode
eflint-repl case_patient_consent.eflint --test-mode
eflint-repl usage-control/case_provenance1.eflint --test-mode
eflint-repl usage-control/case_provenance2.eflint --test-mode
eflint-repl usage-control/case_provenance3.eflint --test-mode
