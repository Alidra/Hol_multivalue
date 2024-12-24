require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8003920 [_141853 _141854 _141855] (s : El (fun (cart _141853 _141854) bool)) (t : El (fun (cart _141853 _141855) bool)) (P : El (fun (cart _141853 (finite_sum _141854 _141855)) bool)) : Prf (= T (= (∀ (λ z : El (cart _141853 (finite_sum _141854 _141855)), (⇒ ((@IN (cart _141853 (finite_sum _141854 _141855))) z ((@PCROSS _141853 _141854 _141855) s t)) (P z)))) (∀ (λ x : El (cart _141853 _141854), (∀ (λ y : El (cart _141853 _141855), (⇒ (∧ ((@IN (cart _141853 _141854)) x s) ((@IN (cart _141853 _141855)) y t)) (P ((@pastecart _141853 _141854 _141855) x y)))))))));
