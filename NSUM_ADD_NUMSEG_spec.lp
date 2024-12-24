require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7040857 : Prf (∀ (λ f : El (fun num num), (∀ (λ g : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (= ((@nsum num) (… m n) (λ i : El num, (+ (f i) (g i)))) (+ ((@nsum num) (… m n) f) ((@nsum num) (… m n) g)))))))))));
