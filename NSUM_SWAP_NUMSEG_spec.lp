require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7047627 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (∀ (λ f : El (fun num (fun num num)), (= ((@nsum num) (… a b) (λ i : El num, ((@nsum num) (… c d) (f i)))) ((@nsum num) (… c d) (λ j : El num, ((@nsum num) (… a b) (λ i : El num, (f i j))))))))))))))));
