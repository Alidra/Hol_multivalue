require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7213740 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (real_le (real_abs ((@sum num) (… m n) f)) ((@sum num) (… m n) (λ i : El num, (real_abs (f i)))))))))));
