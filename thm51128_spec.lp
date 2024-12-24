require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51128 [A B] (a0 : El A) (a1 : El B) : Prf (= a0 ((@ε (fun (prod A B) A)) (λ fn : El (fun (prod A B) A), (∀ (λ a0' : El A, (∀ (λ a1' : El B, (= (fn ((@̦‚ A B) a0' a1')) a0')))))) ((@̦‚ A B) a0 a1)));
