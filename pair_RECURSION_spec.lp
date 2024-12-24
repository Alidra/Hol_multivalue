require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem48206 [A B C] : Prf (∀ (λ PAIR' : El (fun A (fun B C)), (∃ (λ fn : El (fun (prod A B) C), (∀ (λ a0 : El A, (∀ (λ a1 : El B, (= (fn ((@̦‚ A B) a0 a1)) (PAIR' a0 a1))))))))));
