require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8055464 [_143007 _143008 _143009] (s : El (fun (cart _143007 _143008) bool)) (f : El (fun (fun (cart _143007 _143009) bool) bool)) (h1 : Prf (¬ (= f (@EMPTY (fun (cart _143007 _143009) bool))))) : Prf (∀ (λ x : El (cart _143007 _143008), (∀ (λ y : El (cart _143007 _143009), (= (∧ ((@IN (cart _143007 _143008)) x s) ((@IN (cart _143007 _143009)) y ((@INTERS (cart _143007 _143009)) f))) (∀ (λ t : El (fun (cart _143007 _143009) bool), (⇒ ((@IN (fun (cart _143007 _143009) bool)) t f) (∧ ((@IN (cart _143007 _143008)) x s) ((@IN (cart _143007 _143009)) y t))))))))));
