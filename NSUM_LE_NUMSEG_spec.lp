require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7041096 : Prf (∀ (λ f : El (fun num num), (∀ (λ g : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∀ (λ i : El num, (⇒ (∧ (<= m i) (<= i n)) (<= (f i) (g i))))) (<= ((@nsum num) (… m n) f) ((@nsum num) (… m n) g)))))))))));
