require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1163656 [_27338] : Prf (∀ (λ P : El (fun _27338 bool), (∀ (λ l : El (list _27338), (= (∀ (λ i : El num, (⇒ (< i ((@LENGTH _27338) l)) (P ((@EL _27338) i l))))) ((@ALL _27338) P l))))));
