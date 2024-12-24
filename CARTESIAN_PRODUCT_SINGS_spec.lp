require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4434827 [A K] : Prf (∀ (λ k : El (fun K bool), (∀ (λ x : El (fun K A), (⇒ ((@EXTENSIONAL K A) k x) (= ((@cartesian_product A K) k (λ i : El K, ((@INSERT A) (x i) (@EMPTY A)))) ((@INSERT (fun K A)) x (@EMPTY (fun K A)))))))));
