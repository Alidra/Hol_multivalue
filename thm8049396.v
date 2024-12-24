Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8049396_term_abbrevs.
Require Import EXTENSION_spec.
Require Import PASTECART_IN_PCROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Require Import thm7660850_spec.
Require Import thm7662539_spec.
Lemma lem8049121 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term0 _141927 _141928 _141929 s.
Proof. exact (@lem8004229 _141927 _141928 _141929 s). Qed.
Lemma lem8049122 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : (term0 _141927 _141928 _141929 s) = (term1 _141927 _141928 _141929 s).
Proof. exact (eq_refl (term0 _141927 _141928 _141929 s)). Qed.
Lemma lem8049123 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) : term1 _141927 _141928 _141929 s.
Proof. exact (EQ_MP (@lem8049122 _141927 _141928 _141929 s) (@lem8049121 _141927 _141928 _141929 s)). Qed.
Lemma lem8049124 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term2 _141927 _141928 _141929 s t.
Proof. exact (@lem8049123 _141927 _141928 _141929 s t). Qed.
Lemma lem8049125 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term2 _141927 _141928 _141929 s t) = (term3 _141927 _141928 _141929 s t).
Proof. exact (eq_refl (term2 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049126 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term3 _141927 _141928 _141929 s t.
Proof. exact (EQ_MP (@lem8049125 _141927 _141928 _141929 s t) (@lem8049124 _141927 _141928 _141929 s t)). Qed.
Lemma lem8049127 {_141927 _141928 _141929 : Type'} (s : type24 _141927 _141928) (t : type24 _141927 _141929) (x : cart _141927 _141928) : term4 _141927 _141928 _141929 s t x.
Proof. exact (@lem8049126 _141927 _141928 _141929 s t x). Qed.
Lemma lem8049128 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : (term4 _141927 _141928 _141929 s t x) = (term5 _141927 _141928 _141929 x s t).
Proof. exact (eq_refl (term4 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049129 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) : term5 _141927 _141928 _141929 x s t.
Proof. exact (EQ_MP (@lem8049128 _141927 _141928 _141929 x s t) (@lem8049127 _141927 _141928 _141929 s t x)). Qed.
Lemma lem8049130 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (t : type24 _141927 _141929) (y : cart _141927 _141929) : term6 _141927 _141928 _141929 x s t y.
Proof. exact (@lem8049129 _141927 _141928 _141929 x s t y). Qed.
Lemma lem8049131 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term6 _141927 _141928 _141929 x s t y) = ((term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t)).
Proof. exact (eq_refl (term6 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049157 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem8049158 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem8049157 _83095 p). Qed.
Lemma lem8049159 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem8049160 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem8049159 _83095 p) (@lem8049158 _83095 p)). Qed.
Lemma lem8049161 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem8049160 _83095 p x). Qed.
Lemma lem8049162 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem8049171 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8049172 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8049173 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8049172 A s) (@lem8049171 A s)). Qed.
Lemma lem8049174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8049173 A s t). Qed.
Lemma lem8049175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8049192 {_89711 _89725 : Type'} : term18 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem8049193 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term19 _89711 _89725 P.
Proof. exact (@lem8049192 _89711 _89725 P). Qed.
Lemma lem8049194 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term19 _89711 _89725 P) = (term20 _89711 _89725 P).
Proof. exact (eq_refl (term19 _89711 _89725 P)). Qed.
Lemma lem8049195 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term20 _89711 _89725 P.
Proof. exact (EQ_MP (@lem8049194 _89711 _89725 P) (@lem8049193 _89711 _89725 P)). Qed.
Lemma lem8049196 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term21 _89711 _89725 P f.
Proof. exact (@lem8049195 _89711 _89725 P f). Qed.
Lemma lem8049197 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term21 _89711 _89725 P f) = ((term22 _89711 _89725 P f) = (term23 _89711 _89725 P f)).
Proof. exact (eq_refl (term21 _89711 _89725 P f)). Qed.
Lemma lem8049202 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8049175 A s t) (@lem8049174 A s t)). Qed.
Lemma lem8049203 {_142951 _142952 _142953 : Type'} (s : type16 _142951 _142952 _142953) (t : type16 _142951 _142952 _142953) : (s = t) = (term24 _142951 _142952 _142953 s t).
Proof. exact (@lem8049202 (type2 _142951 _142952 _142953) s t). Qed.
Lemma lem8049204 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 g)) = (term27 _142951 _142952 _142953 f g).
Proof. exact (@lem8049203 _142951 _142952 _142953 (term25 _142951 _142952 _142953 f g) (term26 _142951 _142952 _142953 g)). Qed.
Lemma lem8049210 {_140454 _140455 _140456 : Type'} (P : type16 _140454 _140455 _140456) : (term28 _140454 _140455 _140456 P) = (term29 _140454 _140455 _140456 P).
Proof. exact (EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P)). Qed.
Lemma lem8049211 {_142951 _142952 _142953 : Type'} (P : type16 _142951 _142952 _142953) : (term28 _142951 _142952 _142953 P) = (term29 _142951 _142952 _142953 P).
Proof. exact (@lem8049210 _142951 _142952 _142953 P). Qed.
Lemma lem8049212 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term30 _142951 _142952 _142953 f g) = (term31 _142951 _142952 _142953 f g).
Proof. exact (@lem8049211 _142951 _142952 _142953 (term32 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049213 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term33 _142951 _142952 _142953 f g x) = ((term34 _142951 _142952 _142953 x f g) = (term35 _142951 _142952 _142953 x g)).
Proof. exact (eq_refl (term33 _142951 _142952 _142953 f g x)). Qed.
Lemma lem8049214 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term36 _142951 _142952 _142953 f g) = (term32 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : type2 _142951 _142952 _142953 => @lem8049213 _142951 _142952 _142953 f x g)). Qed.
Lemma lem8049215 {_142951 _142952 _142953 : Type'} : (@all (cart _142951 (finite_sum _142952 _142953))) = (@all (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@all (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049216 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term30 _142951 _142952 _142953 f g) = (term27 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049215 _142951 _142952 _142953) (@lem8049214 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049218 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term37 _142951 _142952 _142953 f g) = (term38 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049217) (@lem8049216 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049219 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term39 _142951 _142952 _142953 f g x y) = ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y g)).
Proof. exact (eq_refl (term39 _142951 _142952 _142953 f g x y)). Qed.
Lemma lem8049220 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) : (term42 _142951 _142952 _142953 f g x) = (term43 _142951 _142952 _142953 f x g).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049219 _142951 _142952 _142953 f x y g)). Qed.
Lemma lem8049221 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8049222 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (x : cart _142951 _142952) (g : type56 _142951 _142953) : (term44 _142951 _142952 _142953 f g x) = (term45 _142951 _142952 _142953 f x g).
Proof. exact (MK_COMB (@lem8049221 _142951 _142953) (@lem8049220 _142951 _142952 _142953 f x g)). Qed.
Lemma lem8049223 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term46 _142951 _142952 _142953 f g) = (term47 _142951 _142952 _142953 f g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8049222 _142951 _142952 _142953 f x g)). Qed.
Lemma lem8049224 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8049225 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term31 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8049224 _142951 _142952) (@lem8049223 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049226 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term30 _142951 _142952 _142953 f g) = (term31 _142951 _142952 _142953 f g)) = ((term27 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g)).
Proof. exact (MK_COMB (@lem8049218 _142951 _142952 _142953 f g) (@lem8049225 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049227 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term27 _142951 _142952 _142953 f g) = (term48 _142951 _142952 _142953 f g).
Proof. exact (EQ_MP (@lem8049226 _142951 _142952 _142953 f g) (@lem8049212 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049234 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 g)) = (term48 _142951 _142952 _142953 f g).
Proof. exact (TRANS (@lem8049204 _142951 _142952 _142953 f g) (@lem8049227 _142951 _142952 _142953 f g)). Qed.
Lemma lem8049246 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049131 _141927 _141928 _141929 x s y t) (@lem8049130 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049247 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049246 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049248 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term40 _142951 _142952 _142953 x y f g) = (term49 _142951 _142952 _142953 x f y g).
Proof. exact (@lem8049247 _142951 _142952 _142953 x (@INTERS (cart _142951 _142952) f) y (@INTERS (cart _142951 _142953) g)). Qed.
Lemma lem8049252 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : f = (@EMPTY ((cart _142951 _142952) -> Prop)).
Proof. exact (h1). Qed.
Lemma lem8049253 {_142951 _142952 : Type'} : (@INTERS (cart _142951 _142952)) = (@INTERS (cart _142951 _142952)).
Proof. exact (eq_refl (@INTERS (cart _142951 _142952))). Qed.
Lemma lem8049254 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (@INTERS (cart _142951 _142952) f) = (@INTERS (cart _142951 _142952) (@EMPTY ((cart _142951 _142952) -> Prop))).
Proof. exact (MK_COMB (@lem8049253 _142951 _142952) (@lem8049252 _142951 _142952 f h1)). Qed.
Lemma lem8049255 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x) = (@IN (cart _142951 _142952) x).
Proof. exact (eq_refl (@IN (cart _142951 _142952) x)). Qed.
Lemma lem8049256 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term50 _142951 _142952 x f) = (term51 _142951 _142952 x).
Proof. exact (MK_COMB (@lem8049255 _142951 _142952 x) (@lem8049254 _142951 _142952 f h1)). Qed.
Lemma lem8049257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8049258 {_142951 _142952 : Type'} (x : cart _142951 _142952) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term52 _142951 _142952 x f) = (term53 _142951 _142952 x).
Proof. exact (MK_COMB (@lem8049257) (@lem8049256 _142951 _142952 x f h1)). Qed.
Lemma lem8049259 {_142951 _142953 : Type'} (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term50 _142951 _142953 y g) = (term50 _142951 _142953 y g).
Proof. exact (eq_refl (term50 _142951 _142953 y g)). Qed.
Lemma lem8049260 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term49 _142951 _142952 _142953 x f y g) = (term54 _142951 _142952 _142953 x y g).
Proof. exact (MK_COMB (@lem8049258 _142951 _142952 x f h1) (@lem8049259 _142951 _142953 y g)). Qed.
Lemma lem8049263 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term40 _142951 _142952 _142953 x y f g) = (term54 _142951 _142952 _142953 x y g).
Proof. exact (TRANS (@lem8049248 _142951 _142952 _142953 x f y g) (@lem8049260 _142951 _142952 _142953 x y g f h1)). Qed.
Lemma lem8049264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049265 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term55 _142951 _142952 _142953 x y f g) = (term56 _142951 _142952 _142953 x y g).
Proof. exact (MK_COMB (@lem8049264) (@lem8049263 _142951 _142952 _142953 x y g f h1)). Qed.
Lemma lem8049267 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term22 _89711 _89725 P f) = (term23 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem8049197 _89711 _89725 P f) (@lem8049196 _89711 _89725 P f)). Qed.
Lemma lem8049268 {_142951 _142952 _142953 : Type'} (P : type56 _142951 _142953) (f : type57 _142951 _142952 _142953) : (term57 _142951 _142952 _142953 P f) = (term58 _142951 _142952 _142953 P f).
Proof. exact (@lem8049267 (type2 _142951 _142952 _142953) (type24 _142951 _142953) P f). Qed.
Lemma lem8049269 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term59 _142951 _142952 _142953 g) = (term60 _142951 _142952 _142953 g).
Proof. exact (@lem8049268 _142951 _142952 _142953 (term61 _142951 _142953 g) (term62 _142951 _142952 _142953)). Qed.
Lemma lem8049270 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term63 _142951 _142953 g t) = (@IN ((cart _142951 _142953) -> Prop) t g).
Proof. exact (eq_refl (term63 _142951 _142953 g t)). Qed.
Lemma lem8049271 {_142951 _142952 _142953 : Type'} (GEN_PVAR_365 : type16 _142951 _142952 _142953) : (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_365) = (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_365).
Proof. exact (eq_refl (@SETSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop) GEN_PVAR_365)). Qed.
Lemma lem8049272 {_142951 _142952 _142953 : Type'} (GEN_PVAR_365 : type16 _142951 _142952 _142953) (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term64 _142951 _142952 _142953 GEN_PVAR_365 g t) = (term65 _142951 _142952 _142953 GEN_PVAR_365 t g).
Proof. exact (MK_COMB (@lem8049271 _142951 _142952 _142953 GEN_PVAR_365) (@lem8049270 _142951 _142953 t g)). Qed.
Lemma lem8049273 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142953) : (term66 _142951 _142952 _142953 t) = (@PCROSS _142951 _142952 _142953 (@UNIV (cart _142951 _142952)) t).
Proof. exact (eq_refl (term66 _142951 _142952 _142953 t)). Qed.
Lemma lem8049274 {_142951 _142952 _142953 : Type'} (GEN_PVAR_365 : type16 _142951 _142952 _142953) (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term67 _142951 _142952 _142953 GEN_PVAR_365 g t) = (term68 _142951 _142952 _142953 GEN_PVAR_365 g t).
Proof. exact (MK_COMB (@lem8049272 _142951 _142952 _142953 GEN_PVAR_365 t g) (@lem8049273 _142951 _142952 _142953 t)). Qed.
Lemma lem8049275 {_142951 _142952 _142953 : Type'} (GEN_PVAR_365 : type16 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term69 _142951 _142952 _142953 GEN_PVAR_365 g) = (term70 _142951 _142952 _142953 GEN_PVAR_365 g).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049274 _142951 _142952 _142953 GEN_PVAR_365 g t)). Qed.
Lemma lem8049276 {_142951 _142953 : Type'} : (@ex ((cart _142951 _142953) -> Prop)) = (@ex ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@ex ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049277 {_142951 _142952 _142953 : Type'} (GEN_PVAR_365 : type16 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term71 _142951 _142952 _142953 GEN_PVAR_365 g) = (term72 _142951 _142952 _142953 GEN_PVAR_365 g).
Proof. exact (MK_COMB (@lem8049276 _142951 _142953) (@lem8049275 _142951 _142952 _142953 GEN_PVAR_365 g)). Qed.
Lemma lem8049278 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term73 _142951 _142952 _142953 g) = (term74 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun GEN_PVAR_365 : type16 _142951 _142952 _142953 => @lem8049277 _142951 _142952 _142953 GEN_PVAR_365 g)). Qed.
Lemma lem8049279 {_142951 _142952 _142953 : Type'} : (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049280 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term75 _142951 _142952 _142953 g) = (term76 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049279 _142951 _142952 _142953) (@lem8049278 _142951 _142952 _142953 g)). Qed.
Lemma lem8049281 {_142951 _142952 _142953 : Type'} : (@INTERS (cart _142951 (finite_sum _142952 _142953))) = (@INTERS (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@INTERS (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049282 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term59 _142951 _142952 _142953 g) = (term26 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049281 _142951 _142952 _142953) (@lem8049280 _142951 _142952 _142953 g)). Qed.
Lemma lem8049283 {_142951 _142952 _142953 : Type'} : (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)) = (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop)).
Proof. exact (eq_refl (@eq ((cart _142951 (finite_sum _142952 _142953)) -> Prop))). Qed.
Lemma lem8049284 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term77 _142951 _142952 _142953 g) = (term78 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049283 _142951 _142952 _142953) (@lem8049282 _142951 _142952 _142953 g)). Qed.
Lemma lem8049285 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term63 _142951 _142953 g t) = (@IN ((cart _142951 _142953) -> Prop) t g).
Proof. exact (eq_refl (term63 _142951 _142953 g t)). Qed.
Lemma lem8049286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8049287 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term79 _142951 _142953 g t) = (term80 _142951 _142953 t g).
Proof. exact (MK_COMB (@lem8049286) (@lem8049285 _142951 _142953 t g)). Qed.
Lemma lem8049288 {_142951 _142952 _142953 : Type'} (t : type24 _142951 _142953) : (term66 _142951 _142952 _142953 t) = (@PCROSS _142951 _142952 _142953 (@UNIV (cart _142951 _142952)) t).
Proof. exact (eq_refl (term66 _142951 _142952 _142953 t)). Qed.
Lemma lem8049289 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : (@IN (cart _142951 (finite_sum _142952 _142953)) a) = (@IN (cart _142951 (finite_sum _142952 _142953)) a).
Proof. exact (eq_refl (@IN (cart _142951 (finite_sum _142952 _142953)) a)). Qed.
Lemma lem8049290 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) (t : type24 _142951 _142953) : (term81 _142951 _142952 _142953 a t) = (term82 _142951 _142952 _142953 a t).
Proof. exact (MK_COMB (@lem8049289 _142951 _142952 _142953 a) (@lem8049288 _142951 _142952 _142953 t)). Qed.
Lemma lem8049291 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) (t : type24 _142951 _142953) : (term83 _142951 _142952 _142953 g a t) = (term84 _142951 _142952 _142953 g a t).
Proof. exact (MK_COMB (@lem8049287 _142951 _142953 t g) (@lem8049290 _142951 _142952 _142953 a t)). Qed.
Lemma lem8049292 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term85 _142951 _142952 _142953 g a) = (term86 _142951 _142952 _142953 g a).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049291 _142951 _142952 _142953 g a t)). Qed.
Lemma lem8049293 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049294 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term87 _142951 _142952 _142953 g a) = (term88 _142951 _142952 _142953 g a).
Proof. exact (MK_COMB (@lem8049293 _142951 _142953) (@lem8049292 _142951 _142952 _142953 g a)). Qed.
Lemma lem8049295 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56)). Qed.
Lemma lem8049296 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term89 _142951 _142952 _142953 GEN_PVAR_56 g a) = (term90 _142951 _142952 _142953 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem8049295 _142951 _142952 _142953 GEN_PVAR_56) (@lem8049294 _142951 _142952 _142953 g a)). Qed.
Lemma lem8049297 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049298 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term91 _142951 _142952 _142953 GEN_PVAR_56 g a) = (term92 _142951 _142952 _142953 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem8049296 _142951 _142952 _142953 GEN_PVAR_56 g a) (@lem8049297 _142951 _142952 _142953 a)). Qed.
Lemma lem8049299 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term93 _142951 _142952 _142953 GEN_PVAR_56 g) = (term94 _142951 _142952 _142953 GEN_PVAR_56 g).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049298 _142951 _142952 _142953 GEN_PVAR_56 g a)). Qed.
Lemma lem8049300 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049301 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term95 _142951 _142952 _142953 GEN_PVAR_56 g) = (term96 _142951 _142952 _142953 GEN_PVAR_56 g).
Proof. exact (MK_COMB (@lem8049300 _142951 _142952 _142953) (@lem8049299 _142951 _142952 _142953 GEN_PVAR_56 g)). Qed.
Lemma lem8049302 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term97 _142951 _142952 _142953 g) = (term98 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _142951 _142952 _142953 => @lem8049301 _142951 _142952 _142953 GEN_PVAR_56 g)). Qed.
Lemma lem8049303 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049304 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term60 _142951 _142952 _142953 g) = (term99 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049303 _142951 _142952 _142953) (@lem8049302 _142951 _142952 _142953 g)). Qed.
Lemma lem8049305 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : ((term59 _142951 _142952 _142953 g) = (term60 _142951 _142952 _142953 g)) = ((term26 _142951 _142952 _142953 g) = (term99 _142951 _142952 _142953 g)).
Proof. exact (MK_COMB (@lem8049284 _142951 _142952 _142953 g) (@lem8049304 _142951 _142952 _142953 g)). Qed.
Lemma lem8049306 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term26 _142951 _142952 _142953 g) = (term99 _142951 _142952 _142953 g).
Proof. exact (EQ_MP (@lem8049305 _142951 _142952 _142953 g) (@lem8049269 _142951 _142952 _142953 g)). Qed.
Lemma lem8049319 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term100 _142951 _142952 _142953 x y) = (term100 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term100 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049320 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term41 _142951 _142952 _142953 x y g) = (term101 _142951 _142952 _142953 x y g).
Proof. exact (MK_COMB (@lem8049319 _142951 _142952 _142953 x y) (@lem8049306 _142951 _142952 _142953 g)). Qed.
Lemma lem8049322 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem8049162 _83095 p x) (@lem8049161 _83095 p x)). Qed.
Lemma lem8049323 {_142951 _142952 _142953 : Type'} (p : type16 _142951 _142952 _142953) (x : type2 _142951 _142952 _142953) : (term102 _142951 _142952 _142953 x p) = (p x).
Proof. exact (@lem8049322 (type2 _142951 _142952 _142953) p x). Qed.
Lemma lem8049324 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term103 _142951 _142952 _142953 x y g) = (term104 _142951 _142952 _142953 g x y).
Proof. exact (@lem8049323 _142951 _142952 _142953 (term105 _142951 _142952 _142953 g) (@pastecart _142951 _142952 _142953 x y)). Qed.
Lemma lem8049325 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term106 _142951 _142952 _142953 g a) = (term88 _142951 _142952 _142953 g a).
Proof. exact (eq_refl (term106 _142951 _142952 _142953 g a)). Qed.
Lemma lem8049326 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) : (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56) = (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (cart _142951 (finite_sum _142952 _142953)) GEN_PVAR_56)). Qed.
Lemma lem8049327 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term107 _142951 _142952 _142953 GEN_PVAR_56 g a) = (term90 _142951 _142952 _142953 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem8049326 _142951 _142952 _142953 GEN_PVAR_56) (@lem8049325 _142951 _142952 _142953 g a)). Qed.
Lemma lem8049328 {_142951 _142952 _142953 : Type'} (a : type2 _142951 _142952 _142953) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem8049329 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) (a : type2 _142951 _142952 _142953) : (term108 _142951 _142952 _142953 GEN_PVAR_56 g a) = (term92 _142951 _142952 _142953 GEN_PVAR_56 g a).
Proof. exact (MK_COMB (@lem8049327 _142951 _142952 _142953 GEN_PVAR_56 g a) (@lem8049328 _142951 _142952 _142953 a)). Qed.
Lemma lem8049330 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term109 _142951 _142952 _142953 GEN_PVAR_56 g) = (term94 _142951 _142952 _142953 GEN_PVAR_56 g).
Proof. exact (fun_ext (fun a : type2 _142951 _142952 _142953 => @lem8049329 _142951 _142952 _142953 GEN_PVAR_56 g a)). Qed.
Lemma lem8049331 {_142951 _142952 _142953 : Type'} : (@ex (cart _142951 (finite_sum _142952 _142953))) = (@ex (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@ex (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049332 {_142951 _142952 _142953 : Type'} (GEN_PVAR_56 : type2 _142951 _142952 _142953) (g : type56 _142951 _142953) : (term110 _142951 _142952 _142953 GEN_PVAR_56 g) = (term96 _142951 _142952 _142953 GEN_PVAR_56 g).
Proof. exact (MK_COMB (@lem8049331 _142951 _142952 _142953) (@lem8049330 _142951 _142952 _142953 GEN_PVAR_56 g)). Qed.
Lemma lem8049333 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term111 _142951 _142952 _142953 g) = (term98 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun GEN_PVAR_56 : type2 _142951 _142952 _142953 => @lem8049332 _142951 _142952 _142953 GEN_PVAR_56 g)). Qed.
Lemma lem8049334 {_142951 _142952 _142953 : Type'} : (@GSPEC (cart _142951 (finite_sum _142952 _142953))) = (@GSPEC (cart _142951 (finite_sum _142952 _142953))).
Proof. exact (eq_refl (@GSPEC (cart _142951 (finite_sum _142952 _142953)))). Qed.
Lemma lem8049335 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term112 _142951 _142952 _142953 g) = (term99 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049334 _142951 _142952 _142953) (@lem8049333 _142951 _142952 _142953 g)). Qed.
Lemma lem8049336 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) : (term100 _142951 _142952 _142953 x y) = (term100 _142951 _142952 _142953 x y).
Proof. exact (eq_refl (term100 _142951 _142952 _142953 x y)). Qed.
Lemma lem8049337 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term103 _142951 _142952 _142953 x y g) = (term101 _142951 _142952 _142953 x y g).
Proof. exact (MK_COMB (@lem8049336 _142951 _142952 _142953 x y) (@lem8049335 _142951 _142952 _142953 g)). Qed.
Lemma lem8049338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8049339 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (g : type56 _142951 _142953) : (term113 _142951 _142952 _142953 x y g) = (term114 _142951 _142952 _142953 x y g).
Proof. exact (MK_COMB (@lem8049338) (@lem8049337 _142951 _142952 _142953 x y g)). Qed.
Lemma lem8049340 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term104 _142951 _142952 _142953 g x y) = (term115 _142951 _142952 _142953 g x y).
Proof. exact (eq_refl (term104 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049341 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term103 _142951 _142952 _142953 x y g) = (term104 _142951 _142952 _142953 g x y)) = ((term101 _142951 _142952 _142953 x y g) = (term115 _142951 _142952 _142953 g x y)).
Proof. exact (MK_COMB (@lem8049339 _142951 _142952 _142953 x y g) (@lem8049340 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049342 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term101 _142951 _142952 _142953 x y g) = (term115 _142951 _142952 _142953 g x y).
Proof. exact (EQ_MP (@lem8049341 _142951 _142952 _142953 g x y) (@lem8049324 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049352 {_141927 _141928 _141929 : Type'} (x : cart _141927 _141928) (s : type24 _141927 _141928) (y : cart _141927 _141929) (t : type24 _141927 _141929) : (term7 _141927 _141928 _141929 x y s t) = (term8 _141927 _141928 _141929 x s y t).
Proof. exact (EQ_MP (@lem8049131 _141927 _141928 _141929 x s y t) (@lem8049130 _141927 _141928 _141929 x s t y)). Qed.
Lemma lem8049353 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (s : type24 _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term7 _142951 _142952 _142953 x y s t) = (term8 _142951 _142952 _142953 x s y t).
Proof. exact (@lem8049352 _142951 _142952 _142953 x s y t). Qed.
Lemma lem8049354 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term116 _142951 _142952 _142953 x y t) = (term117 _142951 _142952 _142953 x y t).
Proof. exact (@lem8049353 _142951 _142952 _142953 x (@UNIV (cart _142951 _142952)) y t). Qed.
Lemma lem8049357 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (g : type56 _142951 _142953) : (term80 _142951 _142953 t g) = (term80 _142951 _142953 t g).
Proof. exact (eq_refl (term80 _142951 _142953 t g)). Qed.
Lemma lem8049358 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (t : type24 _142951 _142953) : (term118 _142951 _142952 _142953 g x y t) = (term119 _142951 _142952 _142953 g x y t).
Proof. exact (MK_COMB (@lem8049357 _142951 _142953 t g) (@lem8049354 _142951 _142952 _142953 x y t)). Qed.
Lemma lem8049361 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term120 _142951 _142952 _142953 g x y) = (term121 _142951 _142952 _142953 g x y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8049358 _142951 _142952 _142953 g x y t)). Qed.
Lemma lem8049362 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8049363 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term115 _142951 _142952 _142953 g x y) = (term122 _142951 _142952 _142953 g x y).
Proof. exact (MK_COMB (@lem8049362 _142951 _142953) (@lem8049361 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049370 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term101 _142951 _142952 _142953 x y g) = (term122 _142951 _142952 _142953 g x y).
Proof. exact (TRANS (@lem8049342 _142951 _142952 _142953 g x y) (@lem8049363 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049371 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : (term41 _142951 _142952 _142953 x y g) = (term122 _142951 _142952 _142953 g x y).
Proof. exact (TRANS (@lem8049320 _142951 _142952 _142953 x y g) (@lem8049370 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049372 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : ((term40 _142951 _142952 _142953 x y f g) = (term41 _142951 _142952 _142953 x y g)) = ((term54 _142951 _142952 _142953 x y g) = (term122 _142951 _142952 _142953 g x y)).
Proof. exact (MK_COMB (@lem8049265 _142951 _142952 _142953 x y g f h1) (@lem8049371 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8049377 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term43 _142951 _142952 _142953 f x g) = (term123 _142951 _142952 _142953 g x).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8049372 _142951 _142952 _142953 g x y f h1)). Qed.
Lemma lem8049378 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8049379 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term45 _142951 _142952 _142953 f x g) = (term124 _142951 _142952 _142953 g x).
Proof. exact (MK_COMB (@lem8049378 _142951 _142953) (@lem8049377 _142951 _142952 _142953 g x f h1)). Qed.
Lemma lem8049386 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term47 _142951 _142952 _142953 f g) = (term125 _142951 _142952 _142953 g).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8049379 _142951 _142952 _142953 g x f h1)). Qed.
Lemma lem8049387 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8049388 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term48 _142951 _142952 _142953 f g) = (term126 _142951 _142952 _142953 g).
Proof. exact (MK_COMB (@lem8049387 _142951 _142952) (@lem8049386 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8049395 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 g)) = (term126 _142951 _142952 _142953 g).
Proof. exact (TRANS (@lem8049234 _142951 _142952 _142953 f g) (@lem8049388 _142951 _142952 _142953 g f h1)). Qed.
Lemma lem8049396 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : (term126 _142951 _142952 _142953 g) = ((term25 _142951 _142952 _142953 f g) = (term26 _142951 _142952 _142953 g)).
Proof. exact (SYM (@lem8049395 _142951 _142952 _142953 g f h1)). Qed.
