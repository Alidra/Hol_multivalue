require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7210448 : Prf (∀ (λ f : El (fun num real), (∀ (λ g : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∀ (λ i : El num, (⇒ (∧ (<= m i) (<= i n)) (real_le (f i) (g i))))) (real_le ((@sum num) (… m n) f) ((@sum num) (… m n) g)))))))))));
