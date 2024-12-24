require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4456752 [A B K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ f : El (fun K (fun A B)), (= ((@product_map A B K) k f) (λ x : El (fun K A), ((@RESTRICTION K B) k (λ i : El K, (f i (x i))))))))));
