require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1164506 [_27428 _27429] : Prf (∀ (λ P : El (fun _27429 (fun _27428 bool)), (∀ (λ Q : El (fun _27429 (fun _27428 bool)), (∀ (λ l : El (list _27429), (∀ (λ m : El (list _27428), (= (∧ ((@ALL2 _27429 _27428) P l m) ((@ALL2 _27429 _27428) Q l m)) ((@ALL2 _27429 _27428) (λ x : El _27429, (λ y : El _27428, (∧ (P x y) (Q x y)))) l m))))))))));
