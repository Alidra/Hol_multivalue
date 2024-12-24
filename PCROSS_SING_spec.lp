require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8006149 [_142030 A N] : Prf (∀ (λ x : El (cart A _142030), (∀ (λ y : El (cart A N), (= ((@PCROSS A _142030 N) ((@INSERT (cart A _142030)) x (@EMPTY (cart A _142030))) ((@INSERT (cart A N)) y (@EMPTY (cart A N)))) ((@INSERT (cart A (finite_sum _142030 N))) ((@pastecart A _142030 N) x y) (@EMPTY (cart A (finite_sum _142030 N)))))))));
