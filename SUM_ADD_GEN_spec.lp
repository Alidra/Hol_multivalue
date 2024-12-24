require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7069012 [_131804] : Prf (∀ (λ f : El (fun _131804 real), (∀ (λ g : El (fun _131804 real), (∀ (λ s : El (fun _131804 bool), (⇒ (∧ ((@FINITE _131804) ((@GSPEC _131804) (λ GEN_PVAR_312 : El _131804, (∃ (λ x : El _131804, ((@SETSPEC _131804) GEN_PVAR_312 (∧ ((@IN _131804) x s) (¬ (= (f x) (real_of_num (NUMERAL _0))))) x)))))) ((@FINITE _131804) ((@GSPEC _131804) (λ GEN_PVAR_313 : El _131804, (∃ (λ x : El _131804, ((@SETSPEC _131804) GEN_PVAR_313 (∧ ((@IN _131804) x s) (¬ (= (g x) (real_of_num (NUMERAL _0))))) x))))))) (= ((@sum _131804) s (λ x : El _131804, (real_add (f x) (g x)))) (real_add ((@sum _131804) s f) ((@sum _131804) s g))))))))));
