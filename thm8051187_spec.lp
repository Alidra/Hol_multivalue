require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8051187 [_142951 _142952 _142953] (g : El (fun (fun (cart _142951 _142953) bool) bool)) (f : El (fun (fun (cart _142951 _142952) bool) bool)) (h1 : Prf (= f (@EMPTY (fun (cart _142951 _142952) bool)))) : Prf (∀ (λ x : El (cart _142951 _142952), (∀ (λ y : El (cart _142951 _142953), (= (∧ ((@IN (cart _142951 _142952)) x ((@INTERS (cart _142951 _142952)) (@EMPTY (fun (cart _142951 _142952) bool)))) ((@IN (cart _142951 _142953)) y ((@INTERS (cart _142951 _142953)) g))) (∀ (λ t : El (fun (cart _142951 _142953) bool), (⇒ ((@IN (fun (cart _142951 _142953) bool)) t g) (∧ ((@IN (cart _142951 _142952)) x (@UNIV (cart _142951 _142952))) ((@IN (cart _142951 _142953)) y t))))))))));
