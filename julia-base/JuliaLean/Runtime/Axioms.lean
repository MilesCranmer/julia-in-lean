/-!
The only place where axioms about Julia runtime behaviour may be declared.

Prefer modelling Julia behaviour with definitions; add an axiom here only for a
behaviour that cannot be defined in Lean, and document the Julia fact it stands
for. `Audit.lean` accepts axioms from this module and the three standard Lean
axioms, nothing else.
-/
