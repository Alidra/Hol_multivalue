require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7226629 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (= (real_of_num ((@nsum num) (… m n) f)) ((@sum num) (… m n) (λ i : El num, (real_of_num (f i)))))))))));
