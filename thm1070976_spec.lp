require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070976 [A] : Prf ((λ a : El (recspace A), (∀ (λ list' : El (fun (recspace A) bool), (⇒ (∀ (λ a' : El (recspace A), (⇒ (∨ (= a' ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A)))) (∃ (λ a0 : El A, (∃ (λ a1 : El (recspace A), (∧ (= a' ((λ a0' : El A, (λ a1' : El (recspace A), ((@CONSTR A) (SUC (NUMERAL _0)) a0' ((@FCONS (recspace A)) a1' (λ n : El num, (@BOTTOM A)))))) a0 a1)) (list' a1))))))) (list' a')))) (list' a))))) ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A))));
