require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FORALL_IN_PCROSS_term_abbrevs;
require open hol-light.thm0_spec;
require open hol-light.thm8003920_spec;
opaque symbol lem8003921 [_141853 _141854 _141855] (s : El (type24 _141853 _141854)) (t : El (type24 _141853 _141855)) (P : El (type16 _141853 _141854 _141855)) : Prf (= (term0 _141853 _141854 _141855 s t P) (term1 _141853 _141854 _141855 s t P)) ≔ EQ_MP (@lem8003920 _141853 _141854 _141855 s t P) (@lem0);
