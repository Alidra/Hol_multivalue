require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4457258 [A B K] : Prf (∀ (λ f : El (fun K (fun A B)), (∀ (λ k : El (fun K bool), (∀ (λ x : El (fun K A), (= ((@product_map A B K) k f ((@RESTRICTION K A) k x)) ((@RESTRICTION K B) k (λ i : El K, (f i (x i)))))))))));
