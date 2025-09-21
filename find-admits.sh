#!/bin/bash

# Search for proof holes and axioms
grep --color=always -Enr '\b(Axiom|admit|Admitted|Parameter)\b' --include='*.v' .
