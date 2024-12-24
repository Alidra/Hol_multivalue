require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1069413 [A] : Prf ((λ a : El (recspace A), (∀ (λ option' : El (fun (recspace A) bool), (⇒ (∀ (λ a' : El (recspace A), (⇒ (∨ (= a' ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A)))) (∃ (λ a'' : El A, (= a' ((λ a''' : El A, ((@CONSTR A) (SUC (NUMERAL _0)) a''' (λ n : El num, (@BOTTOM A)))) a''))))) (option' a')))) (option' a))))) ((@CONSTR A) (NUMERAL _0) ((@ε A) (λ v : El A, T)) (λ n : El num, (@BOTTOM A))));
