require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7210209 : Prf (∀ (λ f : El (fun num real), (∀ (λ g : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m n) (λ i : El num, (real_sub (f i) (g i)))) (real_sub ((@sum num) (… m n) f) ((@sum num) (… m n) g)))))))))));
