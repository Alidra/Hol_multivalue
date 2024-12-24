require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1066987 [A B] (a : El A) : Prf ((λ a' : El (recspace (prod A B)), (∀ (λ sum' : El (fun (recspace (prod A B)) bool), (⇒ (∀ (λ a'' : El (recspace (prod A B)), (⇒ (∨ (∃ (λ a''' : El A, (= a'' ((λ a'''' : El A, ((@CONSTR (prod A B)) (NUMERAL _0) ((@̦‚ A B) a'''' ((@ε B) (λ v : El B, T))) (λ n : El num, (@BOTTOM (prod A B))))) a''')))) (∃ (λ a''' : El B, (= a'' ((λ a'''' : El B, ((@CONSTR (prod A B)) (SUC (NUMERAL _0)) ((@̦‚ A B) ((@ε A) (λ v : El A, T)) a'''') (λ n : El num, (@BOTTOM (prod A B))))) a'''))))) (sum' a'')))) (sum' a'))))) ((λ a' : El A, ((@CONSTR (prod A B)) (NUMERAL _0) ((@̦‚ A B) a' ((@ε B) (λ v : El B, T))) (λ n : El num, (@BOTTOM (prod A B))))) a));
