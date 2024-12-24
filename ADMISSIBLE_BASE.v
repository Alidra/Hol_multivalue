Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADMISSIBLE_BASE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import admissible_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem8100085 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term0 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (@lem8093231 _143449 _143452 _143456 _143457 _143462 p). Qed.
Lemma lem8100086 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : (term0 _143449 _143452 _143456 _143457 _143462 p) = (term1 _143449 _143452 _143456 _143457 _143462 p).
Proof. exact (eq_refl (term0 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8100087 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) : term1 _143449 _143452 _143456 _143457 _143462 p.
Proof. exact (EQ_MP (@lem8100086 _143449 _143452 _143456 _143457 _143462 p) (@lem8100085 _143449 _143452 _143456 _143457 _143462 p)). Qed.
Lemma lem8100088 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term2 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (@lem8100087 _143449 _143452 _143456 _143457 _143462 p lt2). Qed.
Lemma lem8100089 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : (term2 _143449 _143452 _143456 _143457 _143462 p lt2) = (term3 _143449 _143452 _143456 _143457 _143462 p lt2).
Proof. exact (eq_refl (term2 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8100090 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) : term3 _143449 _143452 _143456 _143457 _143462 p lt2.
Proof. exact (EQ_MP (@lem8100089 _143449 _143452 _143456 _143457 _143462 p lt2) (@lem8100088 _143449 _143452 _143456 _143457 _143462 p lt2)). Qed.
Lemma lem8100091 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term4 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (@lem8100090 _143449 _143452 _143456 _143457 _143462 p lt2 s). Qed.
Lemma lem8100092 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : (term4 _143449 _143452 _143456 _143457 _143462 p lt2 s) = (term5 _143449 _143452 _143456 _143457 _143462 p lt2 s).
Proof. exact (eq_refl (term4 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8100093 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) : term5 _143449 _143452 _143456 _143457 _143462 p lt2 s.
Proof. exact (EQ_MP (@lem8100092 _143449 _143452 _143456 _143457 _143462 p lt2 s) (@lem8100091 _143449 _143452 _143456 _143457 _143462 p lt2 s)). Qed.
Lemma lem8100094 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t.
Proof. exact (@lem8100093 _143449 _143452 _143456 _143457 _143462 p lt2 s t). Qed.
Lemma lem8100095 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t) = ((@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term7 _143449 _143452 _143456 _143457 _143462 p lt2 s t)).
Proof. exact (eq_refl (term6 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8100126 {_143449 _143452 _143456 _143457 _143462 : Type'} (p : type800 _143452 _143456 _143462) (lt2 : type1470 _143449 _143456) (s : _143462 -> _143449) (t : type801 _143452 _143456 _143457 _143462) : (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (term7 _143449 _143452 _143456 _143457 _143462 p lt2 s t).
Proof. exact (EQ_MP (@lem8100095 _143449 _143452 _143456 _143457 _143462 p lt2 s t) (@lem8100094 _143449 _143452 _143456 _143457 _143462 p lt2 s t)). Qed.
Lemma lem8100127 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : type558 A B P) : (@admissible A B A B P lt2 p s t) = (term8 A B P p lt2 s t).
Proof. exact (@lem8100126 A B A B P p lt2 s t). Qed.
Lemma lem8100128 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term9 A B P lt2 p s t) = (term10 A B P p lt2 s t).
Proof. exact (@lem8100127 A B P p lt2 s (term11 A B P t)). Qed.
Lemma lem8100158 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8100159 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term13 A B P f y) = (f y).
Proof. exact (@lem8100158 (A -> B) (P -> B) f y). Qed.
Lemma lem8100160 {A B P : Type'} (t : P -> A) (f : A -> B) : (term14 A B P t f) = (term15 A B P t f).
Proof. exact (@lem8100159 A B P (term11 A B P t) f). Qed.
Lemma lem8100161 {A B P : Type'} (f : A -> B) (t : P -> A) : (term15 A B P t f) = (term16 A B P f t).
Proof. exact (eq_refl (term15 A B P t f)). Qed.
Lemma lem8100162 {A B P : Type'} (t : P -> A) : (term17 A B P t) = (term11 A B P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8100161 A B P f t)). Qed.
Lemma lem8100163 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem8100164 {A B P : Type'} (t : P -> A) (f : A -> B) : (term14 A B P t f) = (term15 A B P t f).
Proof. exact (MK_COMB (@lem8100162 A B P t) (@lem8100163 A B f)). Qed.
Lemma lem8100165 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8100166 {A B P : Type'} (t : P -> A) (f : A -> B) : (term18 A B P t f) = (term19 A B P t f).
Proof. exact (MK_COMB (@lem8100165 B P) (@lem8100164 A B P t f)). Qed.
Lemma lem8100167 {A B P : Type'} (f : A -> B) (t : P -> A) : (term15 A B P t f) = (term16 A B P f t).
Proof. exact (eq_refl (term15 A B P t f)). Qed.
Lemma lem8100168 {A B P : Type'} (f : A -> B) (t : P -> A) : ((term14 A B P t f) = (term15 A B P t f)) = ((term15 A B P t f) = (term16 A B P f t)).
Proof. exact (MK_COMB (@lem8100166 A B P t f) (@lem8100167 A B P f t)). Qed.
Lemma lem8100169 {A B P : Type'} (f : A -> B) (t : P -> A) : (term15 A B P t f) = (term16 A B P f t).
Proof. exact (EQ_MP (@lem8100168 A B P f t) (@lem8100160 A B P t f)). Qed.
Lemma lem8100170 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8100171 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term20 A B P t f a) = (term21 A B P f t a).
Proof. exact (MK_COMB (@lem8100169 A B P f t) (@lem8100170 P a)). Qed.
Lemma lem8100173 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8100174 {B P : Type'} (f : P -> B) (y : P) : (term22 B P f y) = (f y).
Proof. exact (@lem8100173 P B f y). Qed.
Lemma lem8100175 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term23 A B P f t a) = (term21 A B P f t a).
Proof. exact (@lem8100174 B P (term16 A B P f t) a). Qed.
Lemma lem8100176 {A B P : Type'} (f : A -> B) (t : P -> A) (x : P) : (term21 A B P f t x) = (term24 A B P f t x).
Proof. exact (eq_refl (term21 A B P f t x)). Qed.
Lemma lem8100177 {A B P : Type'} (f : A -> B) (t : P -> A) : (term25 A B P f t) = (term16 A B P f t).
Proof. exact (fun_ext (fun x : P => @lem8100176 A B P f t x)). Qed.
Lemma lem8100178 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8100179 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term23 A B P f t a) = (term21 A B P f t a).
Proof. exact (MK_COMB (@lem8100177 A B P f t) (@lem8100178 P a)). Qed.
Lemma lem8100180 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8100181 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term26 A B P f t a) = (term27 A B P f t a).
Proof. exact (MK_COMB (@lem8100180 B) (@lem8100179 A B P f t a)). Qed.
Lemma lem8100182 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term21 A B P f t a) = (term24 A B P f t a).
Proof. exact (eq_refl (term21 A B P f t a)). Qed.
Lemma lem8100183 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : ((term23 A B P f t a) = (term21 A B P f t a)) = ((term21 A B P f t a) = (term24 A B P f t a)).
Proof. exact (MK_COMB (@lem8100181 A B P f t a) (@lem8100182 A B P f t a)). Qed.
Lemma lem8100184 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term21 A B P f t a) = (term24 A B P f t a).
Proof. exact (EQ_MP (@lem8100183 A B P f t a) (@lem8100175 A B P f t a)). Qed.
Lemma lem8100185 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term20 A B P t f a) = (term24 A B P f t a).
Proof. exact (TRANS (@lem8100171 A B P f t a) (@lem8100184 A B P f t a)). Qed.
Lemma lem8100186 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8100187 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term28 A B P t f a) = (term29 A B P f t a).
Proof. exact (MK_COMB (@lem8100186 B) (@lem8100185 A B P f t a)). Qed.
Lemma lem8100189 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8100190 {A B P : Type'} (f : type558 A B P) (y : A -> B) : (term13 A B P f y) = (f y).
Proof. exact (@lem8100189 (A -> B) (P -> B) f y). Qed.
Lemma lem8100191 {A B P : Type'} (t : P -> A) (g : A -> B) : (term14 A B P t g) = (term15 A B P t g).
Proof. exact (@lem8100190 A B P (term11 A B P t) g). Qed.
Lemma lem8100192 {A B P : Type'} (f : A -> B) (t : P -> A) : (term15 A B P t f) = (term16 A B P f t).
Proof. exact (eq_refl (term15 A B P t f)). Qed.
Lemma lem8100193 {A B P : Type'} (t : P -> A) : (term17 A B P t) = (term11 A B P t).
Proof. exact (fun_ext (fun f : A -> B => @lem8100192 A B P f t)). Qed.
Lemma lem8100194 {A B : Type'} (g : A -> B) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem8100195 {A B P : Type'} (t : P -> A) (g : A -> B) : (term14 A B P t g) = (term15 A B P t g).
Proof. exact (MK_COMB (@lem8100193 A B P t) (@lem8100194 A B g)). Qed.
Lemma lem8100196 {B P : Type'} : (@eq (P -> B)) = (@eq (P -> B)).
Proof. exact (eq_refl (@eq (P -> B))). Qed.
Lemma lem8100197 {A B P : Type'} (t : P -> A) (g : A -> B) : (term18 A B P t g) = (term19 A B P t g).
Proof. exact (MK_COMB (@lem8100196 B P) (@lem8100195 A B P t g)). Qed.
Lemma lem8100198 {A B P : Type'} (g : A -> B) (t : P -> A) : (term15 A B P t g) = (term16 A B P g t).
Proof. exact (eq_refl (term15 A B P t g)). Qed.
Lemma lem8100199 {A B P : Type'} (g : A -> B) (t : P -> A) : ((term14 A B P t g) = (term15 A B P t g)) = ((term15 A B P t g) = (term16 A B P g t)).
Proof. exact (MK_COMB (@lem8100197 A B P t g) (@lem8100198 A B P g t)). Qed.
Lemma lem8100200 {A B P : Type'} (g : A -> B) (t : P -> A) : (term15 A B P t g) = (term16 A B P g t).
Proof. exact (EQ_MP (@lem8100199 A B P g t) (@lem8100191 A B P t g)). Qed.
Lemma lem8100201 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8100202 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term20 A B P t g a) = (term21 A B P g t a).
Proof. exact (MK_COMB (@lem8100200 A B P g t) (@lem8100201 P a)). Qed.
Lemma lem8100204 {A B : Type'} (f : A -> B) (y : A) : (term12 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem8100205 {B P : Type'} (f : P -> B) (y : P) : (term22 B P f y) = (f y).
Proof. exact (@lem8100204 P B f y). Qed.
Lemma lem8100206 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term23 A B P g t a) = (term21 A B P g t a).
Proof. exact (@lem8100205 B P (term16 A B P g t) a). Qed.
Lemma lem8100207 {A B P : Type'} (g : A -> B) (t : P -> A) (x : P) : (term21 A B P g t x) = (term24 A B P g t x).
Proof. exact (eq_refl (term21 A B P g t x)). Qed.
Lemma lem8100208 {A B P : Type'} (g : A -> B) (t : P -> A) : (term25 A B P g t) = (term16 A B P g t).
Proof. exact (fun_ext (fun x : P => @lem8100207 A B P g t x)). Qed.
Lemma lem8100209 {P : Type'} (a : P) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8100210 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term23 A B P g t a) = (term21 A B P g t a).
Proof. exact (MK_COMB (@lem8100208 A B P g t) (@lem8100209 P a)). Qed.
Lemma lem8100211 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8100212 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term26 A B P g t a) = (term27 A B P g t a).
Proof. exact (MK_COMB (@lem8100211 B) (@lem8100210 A B P g t a)). Qed.
Lemma lem8100213 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term21 A B P g t a) = (term24 A B P g t a).
Proof. exact (eq_refl (term21 A B P g t a)). Qed.
Lemma lem8100214 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : ((term23 A B P g t a) = (term21 A B P g t a)) = ((term21 A B P g t a) = (term24 A B P g t a)).
Proof. exact (MK_COMB (@lem8100212 A B P g t a) (@lem8100213 A B P g t a)). Qed.
Lemma lem8100215 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term21 A B P g t a) = (term24 A B P g t a).
Proof. exact (EQ_MP (@lem8100214 A B P g t a) (@lem8100206 A B P g t a)). Qed.
Lemma lem8100216 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term20 A B P t g a) = (term24 A B P g t a).
Proof. exact (TRANS (@lem8100202 A B P g t a) (@lem8100215 A B P g t a)). Qed.
Lemma lem8100217 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : ((term20 A B P t f a) = (term20 A B P t g a)) = ((term24 A B P f t a) = (term24 A B P g t a)).
Proof. exact (MK_COMB (@lem8100187 A B P f t a) (@lem8100216 A B P g t a)). Qed.
Lemma lem8100220 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term30 A B P p lt2 s a f g) = (term30 A B P p lt2 s a f g).
Proof. exact (eq_refl (term30 A B P p lt2 s a f g)). Qed.
Lemma lem8100221 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term31 A B P p lt2 s f t g a) = (term32 A B P p lt2 s f g t a).
Proof. exact (MK_COMB (@lem8100220 A B P p lt2 s a f g) (@lem8100217 A B P f g t a)). Qed.
Lemma lem8100224 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) : (term33 A B P p lt2 s f t g) = (term34 A B P p lt2 s f g t).
Proof. exact (fun_ext (fun a : P => @lem8100221 A B P p lt2 s f g t a)). Qed.
Lemma lem8100225 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100226 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) : (term35 A B P p lt2 s f t g) = (term36 A B P p lt2 s f g t).
Proof. exact (MK_COMB (@lem8100225 P) (@lem8100224 A B P p lt2 s f g t)). Qed.
Lemma lem8100231 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : P -> A) : (term37 A B P p lt2 s f t) = (term38 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8100226 A B P p lt2 s f g t)). Qed.
Lemma lem8100232 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100233 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : P -> A) : (term39 A B P p lt2 s f t) = (term40 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8100232 A B) (@lem8100231 A B P p lt2 s f t)). Qed.
Lemma lem8100238 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term41 A B P p lt2 s t) = (term42 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8100233 A B P p lt2 s f t)). Qed.
Lemma lem8100239 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100240 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term10 A B P p lt2 s t) = (term43 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8100239 A B) (@lem8100238 A B P p lt2 s t)). Qed.
Lemma lem8100245 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term9 A B P lt2 p s t) = (term43 A B P p lt2 s t).
Proof. exact (TRANS (@lem8100128 A B P p lt2 s t) (@lem8100240 A B P p lt2 s t)). Qed.
Lemma lem8100246 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term44 A B P p lt2 t s) = (term44 A B P p lt2 t s).
Proof. exact (eq_refl (term44 A B P p lt2 t s)). Qed.
Lemma lem8100247 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term45 A B P lt2 p s t) = (term46 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8100246 A B P p lt2 t s) (@lem8100245 A B P p lt2 s t)). Qed.
Lemma lem8100250 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term47 A B P lt2 p s) = (term48 A B P p lt2 s).
Proof. exact (fun_ext (fun t : P -> A => @lem8100247 A B P p lt2 s t)). Qed.
Lemma lem8100251 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8100252 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term49 A B P lt2 p s) = (term50 A B P p lt2 s).
Proof. exact (MK_COMB (@lem8100251 A P) (@lem8100250 A B P p lt2 s)). Qed.
Lemma lem8100257 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term51 A B P lt2 p) = (term52 A B P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8100252 A B P p lt2 s)). Qed.
Lemma lem8100258 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8100259 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term53 A B P lt2 p) = (term54 A B P p lt2).
Proof. exact (MK_COMB (@lem8100258 A P) (@lem8100257 A B P p lt2)). Qed.
Lemma lem8100264 {A B P : Type'} (lt2 : type1402 A) : (term55 A B P lt2) = (term56 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8100259 A B P p lt2)). Qed.
Lemma lem8100265 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8100266 {A B P : Type'} (lt2 : type1402 A) : (term57 A B P lt2) = (term58 A B P lt2).
Proof. exact (MK_COMB (@lem8100265 A B P) (@lem8100264 A B P lt2)). Qed.
Lemma lem8100271 {A B P : Type'} : (term59 A B P) = (term60 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8100266 A B P lt2)). Qed.
Lemma lem8100272 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8100273 {A B P : Type'} : (term61 A B P) = (term62 A B P).
Proof. exact (MK_COMB (@lem8100272 A) (@lem8100271 A B P)). Qed.
Lemma lem8100278 {A B P : Type'} : (term62 A B P) = (term61 A B P).
Proof. exact (SYM (@lem8100273 A B P)). Qed.
Lemma lem8100280 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8100281 {A B P : Type'} : (term62 A B P) = (term64 A B P).
Proof. exact (@lem8100280 (term62 A B P)). Qed.
Lemma lem8100282 {A B P : Type'} : (term64 A B P) = (term62 A B P).
Proof. exact (SYM (@lem8100281 A B P)). Qed.
Lemma lem8100283 {A B P : Type'} (h1 : term65 A B P) : term65 A B P.
Proof. exact (h1). Qed.
Lemma lem8100286 {A B P : Type'} (h1 : term64 A B P) : term64 A B P.
Proof. exact (h1). Qed.
Lemma lem8100287 {A B P : Type'} : term66 A B P.
Proof. exact (fun h0 : term64 A B P => @lem8100286 A B P h0). Qed.
Lemma lem8100288 {A B P : Type'} (h1 : term66 A B P) : term66 A B P.
Proof. exact (h1). Qed.
Lemma lem8100289 {A B P : Type'} (h1 : term64 A B P) : term64 A B P.
Proof. exact (h1). Qed.
Lemma lem8100290 {A B P : Type'} (h1 : term64 A B P) (h2 : term66 A B P) : term64 A B P.
Proof. exact (@lem8100288 A B P h2 (@lem8100289 A B P h1)). Qed.
Lemma lem8100291 {A B P : Type'} (h1 : term64 A B P) : term67 A B P.
Proof. exact (fun h0 : term66 A B P => @lem8100290 A B P h1 h0). Qed.
Lemma lem8100292 {A B P : Type'} (h1 : term66 A B P) : term66 A B P.
Proof. exact (h1). Qed.
Lemma lem8100293 {A B P : Type'} (h1 : term64 A B P) (h2 : term66 A B P) : term64 A B P.
Proof. exact (@lem8100291 A B P h1 (@lem8100292 A B P h2)). Qed.
Lemma lem8100294 {A B P : Type'} (h1 : term66 A B P) : term66 A B P.
Proof. exact (fun h0 : term64 A B P => @lem8100293 A B P h0 h1). Qed.
Lemma lem8100295 {A B P : Type'} : term68 A B P.
Proof. exact (fun h0 : term66 A B P => @lem8100294 A B P h0). Qed.
Lemma lem8100298 {A B P : Type'} : term66 A B P.
Proof. exact (@lem8100295 A B P (@lem8100287 A B P)). Qed.
Lemma lem8100299 {A B P : Type'} : term66 A B P.
Proof. exact (@lem8100298 A B P). Qed.
Lemma lem8100301 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8100302 {A B P : Type'} : (term64 A B P) = (term69 A B P).
Proof. exact (@lem8100301 (term65 A B P)). Qed.
Lemma lem8100304 (t : Prop) : (term70 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8100305 {A B P : Type'} : (term69 A B P) = (term62 A B P).
Proof. exact (@lem8100304 (term62 A B P)). Qed.
Lemma lem8100362 {A B P : Type'} : (term64 A B P) = (term62 A B P).
Proof. exact (TRANS (@lem8100302 A B P) (@lem8100305 A B P)). Qed.
Lemma lem8100363 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : ((term24 A B P f t a) = (term24 A B P g t a)) = ((term24 A B P f t a) = (term24 A B P g t a)).
Proof. exact (eq_refl ((term24 A B P f t a) = (term24 A B P g t a))). Qed.
Lemma lem8100368 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term71 A B P lt2 s a f g z) = (term71 A B P lt2 s a f g z).
Proof. exact (eq_refl (term71 A B P lt2 s a f g z)). Qed.
Lemma lem8100369 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term72 A B P lt2 s a f g) = (term72 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8100368 A B P lt2 s a f g z)). Qed.
Lemma lem8100370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8100371 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term73 A B P lt2 s a f g) = (term73 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8100370 A) (@lem8100369 A B P lt2 s a f g)). Qed.
Lemma lem8100374 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term74 A B P p g a) = (term74 A B P p g a).
Proof. exact (eq_refl (term74 A B P p g a)). Qed.
Lemma lem8100375 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term75 A B P p lt2 s a f g) = (term75 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100374 A B P p g a) (@lem8100371 A B P lt2 s a f g)). Qed.
Lemma lem8100378 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term74 A B P p f a) = (term74 A B P p f a).
Proof. exact (eq_refl (term74 A B P p f a)). Qed.
Lemma lem8100379 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term76 A B P p lt2 s a f g) = (term76 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100378 A B P p f a) (@lem8100375 A B P p lt2 s a f g)). Qed.
Lemma lem8100380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8100381 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term30 A B P p lt2 s a f g) = (term30 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100380) (@lem8100379 A B P p lt2 s a f g)). Qed.
Lemma lem8100382 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term32 A B P p lt2 s f g t a) = (term32 A B P p lt2 s f g t a).
Proof. exact (MK_COMB (@lem8100381 A B P p lt2 s a f g) (@lem8100363 A B P f g t a)). Qed.
Lemma lem8100383 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) : (term34 A B P p lt2 s f g t) = (term34 A B P p lt2 s f g t).
Proof. exact (fun_ext (fun a : P => @lem8100382 A B P p lt2 s f g t a)). Qed.
Lemma lem8100384 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100385 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (g : A -> B) (t : P -> A) : (term36 A B P p lt2 s f g t) = (term36 A B P p lt2 s f g t).
Proof. exact (MK_COMB (@lem8100384 P) (@lem8100383 A B P p lt2 s f g t)). Qed.
Lemma lem8100386 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : P -> A) : (term38 A B P p lt2 s f t) = (term38 A B P p lt2 s f t).
Proof. exact (fun_ext (fun g : A -> B => @lem8100385 A B P p lt2 s f g t)). Qed.
Lemma lem8100387 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100388 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (f : A -> B) (t : P -> A) : (term40 A B P p lt2 s f t) = (term40 A B P p lt2 s f t).
Proof. exact (MK_COMB (@lem8100387 A B) (@lem8100386 A B P p lt2 s f t)). Qed.
Lemma lem8100389 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term42 A B P p lt2 s t) = (term42 A B P p lt2 s t).
Proof. exact (fun_ext (fun f : A -> B => @lem8100388 A B P p lt2 s f t)). Qed.
Lemma lem8100390 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100391 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term43 A B P p lt2 s t) = (term43 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8100390 A B) (@lem8100389 A B P p lt2 s t)). Qed.
Lemma lem8100396 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (a : P) : (term77 A B P p f lt2 t s a) = (term77 A B P p f lt2 t s a).
Proof. exact (eq_refl (term77 A B P p f lt2 t s a)). Qed.
Lemma lem8100397 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term78 A B P p f lt2 t s) = (term78 A B P p f lt2 t s).
Proof. exact (fun_ext (fun a : P => @lem8100396 A B P p f lt2 t s a)). Qed.
Lemma lem8100398 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100399 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term79 A B P p f lt2 t s) = (term79 A B P p f lt2 t s).
Proof. exact (MK_COMB (@lem8100398 P) (@lem8100397 A B P p f lt2 t s)). Qed.
Lemma lem8100400 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term80 A B P p lt2 t s) = (term80 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8100399 A B P p f lt2 t s)). Qed.
Lemma lem8100401 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100402 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term81 A B P p lt2 t s) = (term81 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8100401 A B) (@lem8100400 A B P p lt2 t s)). Qed.
Lemma lem8100403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8100404 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term44 A B P p lt2 t s) = (term44 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8100403) (@lem8100402 A B P p lt2 t s)). Qed.
Lemma lem8100405 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : (term46 A B P p lt2 s t) = (term46 A B P p lt2 s t).
Proof. exact (MK_COMB (@lem8100404 A B P p lt2 t s) (@lem8100391 A B P p lt2 s t)). Qed.
Lemma lem8100406 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term48 A B P p lt2 s) = (term48 A B P p lt2 s).
Proof. exact (fun_ext (fun t : P -> A => @lem8100405 A B P p lt2 s t)). Qed.
Lemma lem8100407 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8100408 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : (term50 A B P p lt2 s) = (term50 A B P p lt2 s).
Proof. exact (MK_COMB (@lem8100407 A P) (@lem8100406 A B P p lt2 s)). Qed.
Lemma lem8100409 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term52 A B P p lt2) = (term52 A B P p lt2).
Proof. exact (fun_ext (fun s : P -> A => @lem8100408 A B P p lt2 s)). Qed.
Lemma lem8100410 {A P : Type'} : (@all (P -> A)) = (@all (P -> A)).
Proof. exact (eq_refl (@all (P -> A))). Qed.
Lemma lem8100411 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : (term54 A B P p lt2) = (term54 A B P p lt2).
Proof. exact (MK_COMB (@lem8100410 A P) (@lem8100409 A B P p lt2)). Qed.
Lemma lem8100412 {A B P : Type'} (lt2 : type1402 A) : (term56 A B P lt2) = (term56 A B P lt2).
Proof. exact (fun_ext (fun p : type560 A B P => @lem8100411 A B P p lt2)). Qed.
Lemma lem8100413 {A B P : Type'} : (@all ((A -> B) -> P -> Prop)) = (@all ((A -> B) -> P -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> P -> Prop))). Qed.
Lemma lem8100414 {A B P : Type'} (lt2 : type1402 A) : (term58 A B P lt2) = (term58 A B P lt2).
Proof. exact (MK_COMB (@lem8100413 A B P) (@lem8100412 A B P lt2)). Qed.
Lemma lem8100415 {A B P : Type'} : (term60 A B P) = (term60 A B P).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem8100414 A B P lt2)). Qed.
Lemma lem8100416 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem8100417 {A B P : Type'} : (term62 A B P) = (term62 A B P).
Proof. exact (MK_COMB (@lem8100416 A) (@lem8100415 A B P)). Qed.
Lemma lem8100492 {A B P : Type'} : (term64 A B P) = (term62 A B P).
Proof. exact (TRANS (@lem8100362 A B P) (@lem8100417 A B P)). Qed.
Lemma lem8100493 {A B P : Type'} : (term62 A B P) = (term64 A B P).
Proof. exact (SYM (@lem8100492 A B P)). Qed.
Lemma lem8100494 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term81 A B P p lt2 t s.
Proof. exact (h1). Qed.
Lemma lem8100495 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term76 A B P p lt2 s a f g.
Proof. exact (h1). Qed.
Lemma lem8100497 (p : Prop) : p = (term63 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8100498 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : ((term24 A B P f t a) = (term24 A B P g t a)) = (term82 A B P f g t a).
Proof. exact (@lem8100497 ((term24 A B P f t a) = (term24 A B P g t a))). Qed.
Lemma lem8100499 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term82 A B P f g t a) = ((term24 A B P f t a) = (term24 A B P g t a)).
Proof. exact (SYM (@lem8100498 A B P f g t a)). Qed.
Lemma lem8100500 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) (h1 : term83 A B P f g t a) : term83 A B P f g t a.
Proof. exact (h1). Qed.
Lemma lem8100507 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (a : P) : (term77 A B P p f lt2 t s a) = (term84 A B P p f lt2 t s a).
Proof. exact (@lem17265 (p f a) (term85 A P lt2 t s a)). Qed.
Lemma lem8100508 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term78 A B P p f lt2 t s) = (term86 A B P p f lt2 t s).
Proof. exact (fun_ext (fun a : P => @lem8100507 A B P p f lt2 t s a)). Qed.
Lemma lem8100509 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100510 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term79 A B P p f lt2 t s) = (term87 A B P p f lt2 t s).
Proof. exact (MK_COMB (@lem8100509 P) (@lem8100508 A B P p f lt2 t s)). Qed.
Lemma lem8100511 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term80 A B P p lt2 t s) = (term88 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8100510 A B P p f lt2 t s)). Qed.
Lemma lem8100512 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100569 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term81 A B P p lt2 t s) = (term89 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8100512 A B) (@lem8100511 A B P p lt2 t s)). Qed.
Lemma lem8100570 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term89 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8100569 A B P p lt2 t s) (@lem8100494 A B P p lt2 t s h1)). Qed.
Lemma lem8100579 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term71 A B P lt2 s a f g z) = (term90 A B P lt2 s a f g z).
Proof. exact (@lem17265 (term91 A P lt2 z s a) ((f z) = (g z))). Qed.
Lemma lem8100580 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term72 A B P lt2 s a f g) = (term92 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8100579 A B P lt2 s a f g z)). Qed.
Lemma lem8100581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8100582 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term73 A B P lt2 s a f g) = (term93 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8100581 A) (@lem8100580 A B P lt2 s a f g)). Qed.
Lemma lem8100584 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term74 A B P p g a) = (term74 A B P p g a).
Proof. exact (eq_refl (term74 A B P p g a)). Qed.
Lemma lem8100585 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term75 A B P p lt2 s a f g) = (term94 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100584 A B P p g a) (@lem8100582 A B P lt2 s a f g)). Qed.
Lemma lem8100587 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term74 A B P p f a) = (term74 A B P p f a).
Proof. exact (eq_refl (term74 A B P p f a)). Qed.
Lemma lem8100640 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term76 A B P p lt2 s a f g) = (term95 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100587 A B P p f a) (@lem8100585 A B P p lt2 s a f g)). Qed.
Lemma lem8100641 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term95 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8100640 A B P p lt2 s a f g) (@lem8100495 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100647 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) (h1 : term83 A B P f g t a) : term83 A B P f g t a.
Proof. exact (h1). Qed.
Lemma lem8100666 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (a : P) : (term84 A B P p f lt2 t s a) = (term84 A B P p f lt2 t s a).
Proof. exact (eq_refl (term84 A B P p f lt2 t s a)). Qed.
Lemma lem8100667 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term86 A B P p f lt2 t s) = (term86 A B P p f lt2 t s).
Proof. exact (fun_ext (fun a : P => @lem8100666 A B P p f lt2 t s a)). Qed.
Lemma lem8100668 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100669 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term87 A B P p f lt2 t s) = (term87 A B P p f lt2 t s).
Proof. exact (MK_COMB (@lem8100668 P) (@lem8100667 A B P p f lt2 t s)). Qed.
Lemma lem8100670 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term88 A B P p lt2 t s) = (term88 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8100669 A B P p f lt2 t s)). Qed.
Lemma lem8100671 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100672 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term89 A B P p lt2 t s) = (term89 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8100671 A B) (@lem8100670 A B P p lt2 t s)). Qed.
Lemma lem8100673 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term89 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8100672 A B P p lt2 t s) (@lem8100570 A B P p lt2 t s h1)). Qed.
Lemma lem8100674 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8100679 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8100680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8100679 A B f x). Qed.
Lemma lem8100682 {A B : Type'} (f : A -> B) (z : A) : (f z) = (@I (A -> B) f z).
Proof. exact (@lem8100680 A B f z). Qed.
Lemma lem8100687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8100688 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8100687 A B f x). Qed.
Lemma lem8100690 {A B : Type'} (g : A -> B) (z : A) : (g z) = (@I (A -> B) g z).
Proof. exact (@lem8100688 A B g z). Qed.
Lemma lem8100691 {A B : Type'} (f : A -> B) (z : A) : (term96 A B f z) = (term97 A B f z).
Proof. exact (MK_COMB (@lem8100674 B) (@lem8100682 A B f z)). Qed.
Lemma lem8100692 {A B : Type'} (f : A -> B) (g : A -> B) (z : A) : ((f z) = (g z)) = ((@I (A -> B) f z) = (@I (A -> B) g z)).
Proof. exact (MK_COMB (@lem8100691 A B f z) (@lem8100690 A B g z)). Qed.
Lemma lem8100703 {A P : Type'} (lt2 : type1402 A) (z : A) (s : P -> A) (a : P) : (term98 A P lt2 z s a) = (term98 A P lt2 z s a).
Proof. exact (eq_refl (term98 A P lt2 z s a)). Qed.
Lemma lem8100704 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term90 A B P lt2 s a f g z) = (term99 A B P lt2 s a f g z).
Proof. exact (MK_COMB (@lem8100703 A P lt2 z s a) (@lem8100692 A B f g z)). Qed.
Lemma lem8100705 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term92 A B P lt2 s a f g) = (term100 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8100704 A B P lt2 s a f g z)). Qed.
Lemma lem8100706 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8100707 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term93 A B P lt2 s a f g) = (term101 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8100706 A) (@lem8100705 A B P lt2 s a f g)). Qed.
Lemma lem8100714 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term74 A B P p g a) = (term74 A B P p g a).
Proof. exact (eq_refl (term74 A B P p g a)). Qed.
Lemma lem8100715 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term94 A B P p lt2 s a f g) = (term102 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100714 A B P p g a) (@lem8100707 A B P lt2 s a f g)). Qed.
Lemma lem8100722 {A B P : Type'} (p : type560 A B P) (f : A -> B) (a : P) : (term74 A B P p f a) = (term74 A B P p f a).
Proof. exact (eq_refl (term74 A B P p f a)). Qed.
Lemma lem8100723 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term95 A B P p lt2 s a f g) = (term103 A B P p lt2 s a f g).
Proof. exact (MK_COMB (@lem8100722 A B P p f a) (@lem8100715 A B P p lt2 s a f g)). Qed.
Lemma lem8100724 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term103 A B P p lt2 s a f g.
Proof. exact (EQ_MP (@lem8100723 A B P p lt2 s a f g) (@lem8100641 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100725 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8100726 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem8100733 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8100734 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8100733 A B f x). Qed.
Lemma lem8100736 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term24 A B P f t a) = (term104 A B P f t a).
Proof. exact (@lem8100734 A B f (t a)). Qed.
Lemma lem8100743 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem8100744 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem8100743 A B f x). Qed.
Lemma lem8100746 {A B P : Type'} (g : A -> B) (t : P -> A) (a : P) : (term24 A B P g t a) = (term104 A B P g t a).
Proof. exact (@lem8100744 A B g (t a)). Qed.
Lemma lem8100747 {A B P : Type'} (f : A -> B) (t : P -> A) (a : P) : (term29 A B P f t a) = (term105 A B P f t a).
Proof. exact (MK_COMB (@lem8100726 B) (@lem8100736 A B P f t a)). Qed.
Lemma lem8100748 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : ((term24 A B P f t a) = (term24 A B P g t a)) = ((term104 A B P f t a) = (term104 A B P g t a)).
Proof. exact (MK_COMB (@lem8100747 A B P f t a) (@lem8100746 A B P g t a)). Qed.
Lemma lem8100749 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term83 A B P f g t a) = (term106 A B P f g t a).
Proof. exact (MK_COMB (@lem8100725) (@lem8100748 A B P f g t a)). Qed.
Lemma lem8100751 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term102 A B P p lt2 s a f g.
Proof. exact (proj2 (@lem8100724 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100753 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term101 A B P lt2 s a f g.
Proof. exact (proj2 (@lem8100751 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100762 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (a : P) : (term84 A B P p f lt2 t s a) = (term84 A B P p f lt2 t s a).
Proof. exact (eq_refl (term84 A B P p f lt2 t s a)). Qed.
Lemma lem8100763 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term86 A B P p f lt2 t s) = (term86 A B P p f lt2 t s).
Proof. exact (fun_ext (fun a : P => @lem8100762 A B P p f lt2 t s a)). Qed.
Lemma lem8100764 {P : Type'} : (@all P) = (@all P).
Proof. exact (eq_refl (@all P)). Qed.
Lemma lem8100765 {A B P : Type'} (p : type560 A B P) (f : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term87 A B P p f lt2 t s) = (term87 A B P p f lt2 t s).
Proof. exact (MK_COMB (@lem8100764 P) (@lem8100763 A B P p f lt2 t s)). Qed.
Lemma lem8100766 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term88 A B P p lt2 t s) = (term88 A B P p lt2 t s).
Proof. exact (fun_ext (fun f : A -> B => @lem8100765 A B P p f lt2 t s)). Qed.
Lemma lem8100767 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem8100769 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term89 A B P p lt2 t s) = (term89 A B P p lt2 t s).
Proof. exact (MK_COMB (@lem8100767 A B) (@lem8100766 A B P p lt2 t s)). Qed.
Lemma lem8100770 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term89 A B P p lt2 t s.
Proof. exact (EQ_MP (@lem8100769 A B P p lt2 t s) (@lem8100673 A B P p lt2 t s h1)). Qed.
Lemma lem8100790 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (z : A) : (term99 A B P lt2 s a f g z) = (term99 A B P lt2 s a f g z).
Proof. exact (eq_refl (term99 A B P lt2 s a f g z)). Qed.
Lemma lem8100791 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term100 A B P lt2 s a f g) = (term100 A B P lt2 s a f g).
Proof. exact (fun_ext (fun z : A => @lem8100790 A B P lt2 s a f g z)). Qed.
Lemma lem8100792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8100794 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) : (term101 A B P lt2 s a f g) = (term101 A B P lt2 s a f g).
Proof. exact (MK_COMB (@lem8100792 A) (@lem8100791 A B P lt2 s a f g)). Qed.
Lemma lem8100795 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term101 A B P lt2 s a f g.
Proof. exact (EQ_MP (@lem8100794 A B P lt2 s a f g) (@lem8100753 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100796 {A B P : Type'} (_107438 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term107 A B P p lt2 t s _107438.
Proof. exact (@lem8100770 A B P p lt2 t s h1 _107438). Qed.
Lemma lem8100797 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) : (term107 A B P p lt2 t s _107438) = (term87 A B P p _107438 lt2 t s).
Proof. exact (eq_refl (term107 A B P p lt2 t s _107438)). Qed.
Lemma lem8100798 {A B P : Type'} (_107438 : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term87 A B P p _107438 lt2 t s.
Proof. exact (EQ_MP (@lem8100797 A B P p _107438 lt2 t s) (@lem8100796 A B P _107438 p lt2 t s h1)). Qed.
Lemma lem8100799 {A B P : Type'} (_107438 : A -> B) (_107439 : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term108 A B P p _107438 lt2 t s _107439.
Proof. exact (@lem8100798 A B P _107438 p lt2 t s h1 _107439). Qed.
Lemma lem8100800 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (_107439 : P) : (term108 A B P p _107438 lt2 t s _107439) = (term84 A B P p _107438 lt2 t s _107439).
Proof. exact (eq_refl (term108 A B P p _107438 lt2 t s _107439)). Qed.
Lemma lem8100802 {A B P : Type'} (_107440 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term109 A B P lt2 s a f g _107440.
Proof. exact (@lem8100795 A B P p lt2 s a f g h1 _107440). Qed.
Lemma lem8100803 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107440 : A) : (term109 A B P lt2 s a f g _107440) = (term99 A B P lt2 s a f g _107440).
Proof. exact (eq_refl (term109 A B P lt2 s a f g _107440)). Qed.
Lemma lem8100810 {A B P : Type'} (_107438 : A -> B) (_107439 : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term84 A B P p _107438 lt2 t s _107439.
Proof. exact (EQ_MP (@lem8100800 A B P p _107438 lt2 t s _107439) (@lem8100799 A B P _107438 _107439 p lt2 t s h1)). Qed.
Lemma lem8100812 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) (h1 : term83 A B P f g t a) : term106 A B P f g t a.
Proof. exact (EQ_MP (@lem8100749 A B P f g t a) (@lem8100647 A B P f g t a h1)). Qed.
Lemma lem8100822 {A B P : Type'} (_107440 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term99 A B P lt2 s a f g _107440.
Proof. exact (EQ_MP (@lem8100803 A B P lt2 s a f g _107440) (@lem8100802 A B P _107440 p lt2 s a f g h1)). Qed.
Lemma lem8100901 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : p g a.
Proof. exact (proj1 (@lem8100751 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100902 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term110 A B P p g a.
Proof. exact (fun h0 : term111 A B P p g a => @lem8100901 A B P p lt2 s a f g h1). Qed.
Lemma lem8100904 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8100905 {A B P : Type'} (p : type560 A B P) (g : A -> B) (a : P) : (term110 A B P p g a) = (p g a).
Proof. exact (@lem8100904 (p g a)). Qed.
Lemma lem8100906 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : p g a.
Proof. exact (EQ_MP (@lem8100905 A B P p g a) (@lem8100902 A B P p lt2 s a f g h1)). Qed.
Lemma lem8100912 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8100913 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term84 A B P p _107438 lt2 t s _107439) = (term113 A B P lt2 t s p _107438 _107439).
Proof. exact (@lem8100912 (term85 A P lt2 t s _107439) (term111 A B P p _107438 _107439)). Qed.
Lemma lem8100919 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8100920 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term114 A B P p _107438 lt2 t s _107439) = (term115 A B P lt2 t s p _107438 _107439).
Proof. exact (MK_COMB (@lem8100919) (@lem8100913 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100926 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term113 A B P lt2 t s p _107438 _107439) = (term113 A B P lt2 t s p _107438 _107439).
Proof. exact (eq_refl (term113 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100927 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : ((term84 A B P p _107438 lt2 t s _107439) = (term113 A B P lt2 t s p _107438 _107439)) = ((term113 A B P lt2 t s p _107438 _107439) = (term113 A B P lt2 t s p _107438 _107439)).
Proof. exact (MK_COMB (@lem8100920 A B P lt2 t s p _107438 _107439) (@lem8100926 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8100930 (x : Prop) : (x = x) = True.
Proof. exact (@lem8100929 Prop x). Qed.
Lemma lem8100931 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : ((term113 A B P lt2 t s p _107438 _107439) = (term113 A B P lt2 t s p _107438 _107439)) = True.
Proof. exact (@lem8100930 (term113 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100932 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : ((term84 A B P p _107438 lt2 t s _107439) = (term113 A B P lt2 t s p _107438 _107439)) = True.
Proof. exact (TRANS (@lem8100927 A B P lt2 t s p _107438 _107439) (@lem8100931 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100933 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : True = ((term84 A B P p _107438 lt2 t s _107439) = (term113 A B P lt2 t s p _107438 _107439)).
Proof. exact (SYM (@lem8100932 A B P lt2 t s p _107438 _107439)). Qed.
Lemma lem8100934 {A B P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term84 A B P p _107438 lt2 t s _107439) = (term113 A B P lt2 t s p _107438 _107439).
Proof. exact (EQ_MP (@lem8100933 A B P lt2 t s p _107438 _107439) (@lem0)). Qed.
Lemma lem8100935 {A B P : Type'} (_107438 : A -> B) (_107439 : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term113 A B P lt2 t s p _107438 _107439.
Proof. exact (EQ_MP (@lem8100934 A B P lt2 t s p _107438 _107439) (@lem8100810 A B P _107438 _107439 p lt2 t s h1)). Qed.
Lemma lem8100937 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8100938 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (_107439 : P) : (term113 A B P lt2 t s p _107438 _107439) = (term117 A B P p _107438 lt2 t s _107439).
Proof. exact (@lem8100937 (term111 A B P p _107438 _107439) (term85 A P lt2 t s _107439)). Qed.
Lemma lem8100940 (a : Prop) : (term70 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8100941 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term118 A B P p _107438 _107439) = (p _107438 _107439).
Proof. exact (@lem8100940 (p _107438 _107439)). Qed.
Lemma lem8100942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8100943 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (_107439 : P) : (term119 A B P p _107438 _107439) = (term120 A B P p _107438 _107439).
Proof. exact (MK_COMB (@lem8100942) (@lem8100941 A B P p _107438 _107439)). Qed.
Lemma lem8100944 {A P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (_107439 : P) : (term85 A P lt2 t s _107439) = (term85 A P lt2 t s _107439).
Proof. exact (eq_refl (term85 A P lt2 t s _107439)). Qed.
Lemma lem8100945 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (_107439 : P) : (term117 A B P p _107438 lt2 t s _107439) = (term77 A B P p _107438 lt2 t s _107439).
Proof. exact (MK_COMB (@lem8100943 A B P p _107438 _107439) (@lem8100944 A P lt2 t s _107439)). Qed.
Lemma lem8100946 {A B P : Type'} (p : type560 A B P) (_107438 : A -> B) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (_107439 : P) : (term113 A B P lt2 t s p _107438 _107439) = (term77 A B P p _107438 lt2 t s _107439).
Proof. exact (TRANS (@lem8100938 A B P p _107438 lt2 t s _107439) (@lem8100945 A B P p _107438 lt2 t s _107439)). Qed.
Lemma lem8100949 {A B P : Type'} (_107438 : A -> B) (_107439 : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term77 A B P p _107438 lt2 t s _107439.
Proof. exact (EQ_MP (@lem8100946 A B P p _107438 lt2 t s _107439) (@lem8100935 A B P _107438 _107439 p lt2 t s h1)). Qed.
Lemma lem8100950 {A B P : Type'} (_107438 : A -> B) (_107439 : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term77 A B P p _107438 lt2 t s _107439.
Proof. exact (@lem8100949 A B P _107438 _107439 p lt2 t s h1). Qed.
Lemma lem8100951 {A B P : Type'} (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term77 A B P p g lt2 t s a.
Proof. exact (@lem8100950 A B P g a p lt2 t s h1). Qed.
Lemma lem8100954 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : term85 A P lt2 t s a.
Proof. exact (@lem8100951 A B P g a p lt2 t s h1 (@lem8100906 A B P p lt2 s a f g h2)). Qed.
Lemma lem8100955 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : term121 A P lt2 t s a.
Proof. exact (fun h0 : term122 A P lt2 t s a => @lem8100954 A B P t p lt2 s a f g h1 h2). Qed.
Lemma lem8100957 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8100958 {A P : Type'} (lt2 : type1402 A) (t : P -> A) (s : P -> A) (a : P) : (term121 A P lt2 t s a) = (term85 A P lt2 t s a).
Proof. exact (@lem8100957 (term85 A P lt2 t s a)). Qed.
Lemma lem8100959 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : term85 A P lt2 t s a.
Proof. exact (EQ_MP (@lem8100958 A P lt2 t s a) (@lem8100955 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8100965 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem8100966 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term99 A B P lt2 s a f g _107440) = (term123 A B P f g lt2 _107440 s a).
Proof. exact (@lem8100965 ((@I (A -> B) f _107440) = (@I (A -> B) g _107440)) (term124 A P lt2 _107440 s a)). Qed.
Lemma lem8100974 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8100975 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term125 A B P lt2 s a f g _107440) = (term126 A B P f g lt2 _107440 s a).
Proof. exact (MK_COMB (@lem8100974) (@lem8100966 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100983 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term123 A B P f g lt2 _107440 s a) = (term123 A B P f g lt2 _107440 s a).
Proof. exact (eq_refl (term123 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100984 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : ((term99 A B P lt2 s a f g _107440) = (term123 A B P f g lt2 _107440 s a)) = ((term123 A B P f g lt2 _107440 s a) = (term123 A B P f g lt2 _107440 s a)).
Proof. exact (MK_COMB (@lem8100975 A B P f g lt2 _107440 s a) (@lem8100983 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem8100987 (x : Prop) : (x = x) = True.
Proof. exact (@lem8100986 Prop x). Qed.
Lemma lem8100988 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : ((term123 A B P f g lt2 _107440 s a) = (term123 A B P f g lt2 _107440 s a)) = True.
Proof. exact (@lem8100987 (term123 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100989 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : ((term99 A B P lt2 s a f g _107440) = (term123 A B P f g lt2 _107440 s a)) = True.
Proof. exact (TRANS (@lem8100984 A B P f g lt2 _107440 s a) (@lem8100988 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100990 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : True = ((term99 A B P lt2 s a f g _107440) = (term123 A B P f g lt2 _107440 s a)).
Proof. exact (SYM (@lem8100989 A B P f g lt2 _107440 s a)). Qed.
Lemma lem8100991 {A B P : Type'} (f : A -> B) (g : A -> B) (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term99 A B P lt2 s a f g _107440) = (term123 A B P f g lt2 _107440 s a).
Proof. exact (EQ_MP (@lem8100990 A B P f g lt2 _107440 s a) (@lem0)). Qed.
Lemma lem8100992 {A B P : Type'} (_107440 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term123 A B P f g lt2 _107440 s a.
Proof. exact (EQ_MP (@lem8100991 A B P f g lt2 _107440 s a) (@lem8100822 A B P _107440 p lt2 s a f g h1)). Qed.
Lemma lem8100994 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem8100995 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107440 : A) : (term123 A B P f g lt2 _107440 s a) = (term127 A B P lt2 s a f g _107440).
Proof. exact (@lem8100994 (term124 A P lt2 _107440 s a) ((@I (A -> B) f _107440) = (@I (A -> B) g _107440))). Qed.
Lemma lem8100997 (a : Prop) : (term70 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem8100998 {A P : Type'} (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term128 A P lt2 _107440 s a) = (term91 A P lt2 _107440 s a).
Proof. exact (@lem8100997 (term91 A P lt2 _107440 s a)). Qed.
Lemma lem8100999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8101000 {A P : Type'} (lt2 : type1402 A) (_107440 : A) (s : P -> A) (a : P) : (term129 A P lt2 _107440 s a) = (term130 A P lt2 _107440 s a).
Proof. exact (MK_COMB (@lem8100999) (@lem8100998 A P lt2 _107440 s a)). Qed.
Lemma lem8101001 {A B : Type'} (f : A -> B) (g : A -> B) (_107440 : A) : ((@I (A -> B) f _107440) = (@I (A -> B) g _107440)) = ((@I (A -> B) f _107440) = (@I (A -> B) g _107440)).
Proof. exact (eq_refl ((@I (A -> B) f _107440) = (@I (A -> B) g _107440))). Qed.
Lemma lem8101002 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107440 : A) : (term127 A B P lt2 s a f g _107440) = (term131 A B P lt2 s a f g _107440).
Proof. exact (MK_COMB (@lem8101000 A P lt2 _107440 s a) (@lem8101001 A B f g _107440)). Qed.
Lemma lem8101003 {A B P : Type'} (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (_107440 : A) : (term123 A B P f g lt2 _107440 s a) = (term131 A B P lt2 s a f g _107440).
Proof. exact (TRANS (@lem8100995 A B P lt2 s a f g _107440) (@lem8101002 A B P lt2 s a f g _107440)). Qed.
Lemma lem8101006 {A B P : Type'} (_107440 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term131 A B P lt2 s a f g _107440.
Proof. exact (EQ_MP (@lem8101003 A B P lt2 s a f g _107440) (@lem8100992 A B P _107440 p lt2 s a f g h1)). Qed.
Lemma lem8101007 {A B P : Type'} (_107440 : A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term131 A B P lt2 s a f g _107440.
Proof. exact (@lem8101006 A B P _107440 p lt2 s a f g h1). Qed.
Lemma lem8101008 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term76 A B P p lt2 s a f g) : term132 A B P lt2 s f g t a.
Proof. exact (@lem8101007 A B P (t a) p lt2 s a f g h1). Qed.
Lemma lem8101011 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : (term104 A B P f t a) = (term104 A B P g t a).
Proof. exact (@lem8101008 A B P t p lt2 s a f g h2 (@lem8100959 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8101012 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : term133 A B P f g t a.
Proof. exact (fun h0 : term106 A B P f g t a => @lem8101011 A B P t p lt2 s a f g h1 h2). Qed.
Lemma lem8101014 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8101015 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term133 A B P f g t a) = ((term104 A B P f t a) = (term104 A B P g t a)).
Proof. exact (@lem8101014 ((term104 A B P f t a) = (term104 A B P g t a))). Qed.
Lemma lem8101016 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : (term104 A B P f t a) = (term104 A B P g t a).
Proof. exact (EQ_MP (@lem8101015 A B P f g t a) (@lem8101012 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8101019 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8101021 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) : (term106 A B P f g t a) = (term134 A B P f g t a).
Proof. exact (@lem8101019 ((term104 A B P f t a) = (term104 A B P g t a))). Qed.
Lemma lem8101024 {A B P : Type'} (f : A -> B) (g : A -> B) (t : P -> A) (a : P) (h1 : term83 A B P f g t a) : term134 A B P f g t a.
Proof. exact (EQ_MP (@lem8101021 A B P f g t a) (@lem8100812 A B P f g t a h1)). Qed.
Lemma lem8101027 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : False.
Proof. exact (@lem8101024 A B P f g t a h2 (@lem8101016 A B P t p lt2 s a f g h1 h3)). Qed.
Lemma lem8101028 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : term135.
Proof. exact (fun h0 : ~ False => @lem8101027 A B P t p lt2 s a f g h1 h2 h3). Qed.
Lemma lem8101030 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8101031 : term135 = False.
Proof. exact (@lem8101030 False). Qed.
Lemma lem8101032 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8101031) (@lem8101028 A B P t p lt2 s a f g h1 h2 h3)). Qed.
Lemma lem8101033 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : (term83 A B P f g t a) = False.
Proof. exact (prop_ext (fun h4 : term83 A B P f g t a => @lem8101032 A B P t p lt2 s a f g h1 h2 h3) (fun h4 : False => @lem8100647 A B P f g t a h2)). Qed.
Lemma lem8101034 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8101033 A B P t p lt2 s a f g h1 h2 h3) (@lem8100647 A B P f g t a h2)). Qed.
Lemma lem8101035 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : (term83 A B P f g t a) = False.
Proof. exact (prop_ext (fun h4 : term83 A B P f g t a => @lem8101034 A B P t p lt2 s a f g h1 h2 h3) (fun h4 : False => @lem8100500 A B P f g t a h2)). Qed.
Lemma lem8101036 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term83 A B P f g t a) (h3 : term76 A B P p lt2 s a f g) : False.
Proof. exact (EQ_MP (@lem8101035 A B P t p lt2 s a f g h1 h2 h3) (@lem8100500 A B P f g t a h2)). Qed.
Lemma lem8101037 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : term82 A B P f g t a.
Proof. exact (fun h0 : term83 A B P f g t a => @lem8101036 A B P t p lt2 s a f g h1 h0 h2). Qed.
Lemma lem8101038 {A B P : Type'} (t : P -> A) (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (a : P) (f : A -> B) (g : A -> B) (h1 : term81 A B P p lt2 t s) (h2 : term76 A B P p lt2 s a f g) : (term24 A B P f t a) = (term24 A B P g t a).
Proof. exact (EQ_MP (@lem8100499 A B P f g t a) (@lem8101037 A B P t p lt2 s a f g h1 h2)). Qed.
Lemma lem8101039 {A B P : Type'} (f : A -> B) (g : A -> B) (a : P) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term32 A B P p lt2 s f g t a.
Proof. exact (fun h0 : term76 A B P p lt2 s a f g => @lem8101038 A B P t p lt2 s a f g h1 h0). Qed.
Lemma lem8101044 {A B P : Type'} (f : A -> B) (g : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term36 A B P p lt2 s f g t.
Proof. exact (fun a : P => @lem8101039 A B P f g a p lt2 t s h1). Qed.
Lemma lem8101049 {A B P : Type'} (f : A -> B) (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term40 A B P p lt2 s f t.
Proof. exact (fun g : A -> B => @lem8101044 A B P f g p lt2 t s h1). Qed.
Lemma lem8101054 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (t : P -> A) (s : P -> A) (h1 : term81 A B P p lt2 t s) : term43 A B P p lt2 s t.
Proof. exact (fun f : A -> B => @lem8101049 A B P f p lt2 t s h1). Qed.
Lemma lem8101055 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) (t : P -> A) : term46 A B P p lt2 s t.
Proof. exact (fun h0 : term81 A B P p lt2 t s => @lem8101054 A B P p lt2 t s h0). Qed.
Lemma lem8101060 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) (s : P -> A) : term50 A B P p lt2 s.
Proof. exact (fun t : P -> A => @lem8101055 A B P p lt2 s t). Qed.
Lemma lem8101065 {A B P : Type'} (p : type560 A B P) (lt2 : type1402 A) : term54 A B P p lt2.
Proof. exact (fun s : P -> A => @lem8101060 A B P p lt2 s). Qed.
Lemma lem8101070 {A B P : Type'} (lt2 : type1402 A) : term58 A B P lt2.
Proof. exact (fun p : type560 A B P => @lem8101065 A B P p lt2). Qed.
Lemma lem8101075 {A B P : Type'} : term62 A B P.
Proof. exact (fun lt2 : type1402 A => @lem8101070 A B P lt2). Qed.
Lemma lem8101076 {A B P : Type'} : term64 A B P.
Proof. exact (EQ_MP (@lem8100493 A B P) (@lem8101075 A B P)). Qed.
Lemma lem8101078 {A B P : Type'} : term64 A B P.
Proof. exact (@lem8100299 A B P (@lem8101076 A B P)). Qed.
Lemma lem8101079 {A B P : Type'} (h1 : term65 A B P) : False.
Proof. exact (@lem8101078 A B P (@lem8100283 A B P h1)). Qed.
Lemma lem8101080 {A B P : Type'} (h1 : term65 A B P) : (term65 A B P) = False.
Proof. exact (prop_ext (fun h2 : term65 A B P => @lem8101079 A B P h1) (fun h2 : False => @lem8100283 A B P h1)). Qed.
Lemma lem8101081 {A B P : Type'} (h1 : term65 A B P) : False.
Proof. exact (EQ_MP (@lem8101080 A B P h1) (@lem8100283 A B P h1)). Qed.
Lemma lem8101082 {A B P : Type'} : term64 A B P.
Proof. exact (fun h0 : term65 A B P => @lem8101081 A B P h0). Qed.
Lemma lem8101083 {A B P : Type'} : term62 A B P.
Proof. exact (EQ_MP (@lem8100282 A B P) (@lem8101082 A B P)). Qed.
Lemma lem8101084 {A B P : Type'} : term61 A B P.
Proof. exact (EQ_MP (@lem8100278 A B P) (@lem8101083 A B P)). Qed.
