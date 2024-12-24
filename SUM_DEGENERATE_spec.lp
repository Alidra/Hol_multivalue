require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7067459 [_131446] : Prf (∀ (λ f : El (fun _131446 real), (∀ (λ s : El (fun _131446 bool), (⇒ (¬ ((@FINITE _131446) ((@GSPEC _131446) (λ GEN_PVAR_311 : El _131446, (∃ (λ x : El _131446, ((@SETSPEC _131446) GEN_PVAR_311 (∧ ((@IN _131446) x s) (¬ (= (f x) (real_of_num (NUMERAL _0))))) x))))))) (= ((@sum _131446) s f) (real_of_num (NUMERAL _0))))))));
