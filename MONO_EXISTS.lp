require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.MONO_EXISTS_term_abbrevs;
require open hol-light.thm7400_spec;
opaque symbol lem7401 [A] (P : El (fun A bool)) (Q : El (fun A bool)) : Prf (term0 A P Q) ≔ λ h0 : Prf (term1 A P Q), (@lem7400 A P Q h0);
