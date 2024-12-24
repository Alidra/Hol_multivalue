require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7222072 : Prf (∀ (λ a : El num, (∀ (λ b : El num, (∀ (λ c : El num, (∀ (λ d : El num, (∀ (λ f : El (fun num (fun num real)), (= ((@sum num) (… a b) (λ i : El num, ((@sum num) (… c d) (f i)))) ((@sum num) (… c d) (λ j : El num, ((@sum num) (… a b) (λ i : El num, (f i j))))))))))))))));
