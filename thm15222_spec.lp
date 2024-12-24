require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem15222 [_2963] (g : El bool) (t : El _2963) (e : El _2963) (g' : El bool) (t' : El _2963) (e' : El _2963) : Prf (⇒ (= g g') (⇒ (⇒ g' (= t t')) (⇒ (⇒ (¬ g') (= e e')) (= ((@COND _2963) g t e) ((@COND _2963) g' t' e')))));
