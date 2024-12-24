require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7210115 : Prf (∀ (λ f : El (fun num real), (∀ (λ g : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) (λ i : El num, (real_add (f i) (g i)))) (real_add ((@sum num) (… m n) f) ((@sum num) (… m n) g)))))))))));
