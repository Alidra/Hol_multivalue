require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7157061 [_133899] : Prf (∀ (λ P : El (fun _133899 bool), (∀ (λ s : El (fun _133899 bool), (∀ (λ f : El (fun _133899 real), (= ((@sum _133899) ((@GSPEC _133899) (λ GEN_PVAR_316 : El _133899, (∃ (λ x : El _133899, ((@SETSPEC _133899) GEN_PVAR_316 (∧ ((@IN _133899) x s) (P x)) x))))) f) ((@sum _133899) s (λ x : El _133899, ((@COND real) (P x) (f x) (real_of_num (NUMERAL _0))))))))))));
