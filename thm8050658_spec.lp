require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8050658 [_143061 _143062 _143063] (t : El (fun (cart _143061 _143063) bool)) (f : El (fun (fun (cart _143061 _143062) bool) bool)) (h1 : Prf (= f (@EMPTY (fun (cart _143061 _143062) bool)))) : Prf (= (∀ (λ x : El (cart _143061 _143062), (∀ (λ y : El (cart _143061 _143063), (= (∧ ((@IN (cart _143061 _143062)) x ((@INTERS (cart _143061 _143062)) (@EMPTY (fun (cart _143061 _143062) bool)))) ((@IN (cart _143061 _143063)) y t)) (∧ ((@IN (cart _143061 _143062)) x (@UNIV (cart _143061 _143062))) ((@IN (cart _143061 _143063)) y t))))))) (= ((@PCROSS _143061 _143062 _143063) ((@INTERS (cart _143061 _143062)) f) t) ((@PCROSS _143061 _143062 _143063) (@UNIV (cart _143061 _143062)) t)));
