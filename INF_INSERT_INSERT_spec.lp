require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5259530 : Prf (∀ (λ a : El real, (∀ (λ b : El real, (∀ (λ s : El (fun real bool), (= (inf ((@INSERT real) b ((@INSERT real) a s))) (inf ((@INSERT real) (real_min a b) s)))))))));
