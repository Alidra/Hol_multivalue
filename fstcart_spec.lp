require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7633949 [A M N] : Prf (∀ (λ f : El (cart A (finite_sum M N)), (= ((@fstcart A M N) f) ((@lambda A M) (λ i : El num, ((@﹩ A (finite_sum M N)) f i))))));
