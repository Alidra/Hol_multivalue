require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3306761 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (∀ (λ x' : El A, (= (= ((@IN A) x s) ((@IN A) x' s)) (= ((@IN A) x ((@DELETE A) s x')) ((@IN A) x' ((@DELETE A) s x))))))))));
