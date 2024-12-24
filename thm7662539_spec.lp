require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7662539 [_140454 _140455 _140456] (P : El (fun (cart _140454 (finite_sum _140455 _140456)) bool)) : Prf (⇒ (¬ (= (∀ (λ p : El (cart _140454 (finite_sum _140455 _140456)), (P p))) (∀ (λ x : El (cart _140454 _140455), (∀ (λ y : El (cart _140454 _140456), (P ((@pastecart _140454 _140455 _140456) x y)))))))) F);
