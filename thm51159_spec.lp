require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem51159 [A B] (a0 : El A) (a1 : El B) : Prf (= a1 ((@ε (fun (prod A B) B)) (λ fn : El (fun (prod A B) B), (∀ (λ a0' : El A, (∀ (λ a1' : El B, (= (fn ((@̦‚ A B) a0' a1')) a1')))))) ((@̦‚ A B) a0 a1)));
