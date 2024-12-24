require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1068060 [A B Z] : Prf (∀ (λ INL' : El (fun A Z), (∀ (λ INR' : El (fun B Z), (∃ (λ fn : El (fun (Sum A B) Z), (∧ (∀ (λ a : El A, (= (fn ((@INL A B) a)) (INL' a)))) (∀ (λ a : El B, (= (fn ((@INR A B) a)) (INR' a)))))))))));
