Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4374285_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem4374007 {_103718 _103721 : Type'} (x : _103718) : term0 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4374008 {_103718 _103721 : Type'} (x : _103718) : (term0 _103718 _103721 x) = (term1 _103718 _103721 x).
Proof. exact (eq_refl (term0 _103718 _103721 x)). Qed.
Lemma lem4374009 {_103718 _103721 : Type'} (x : _103718) : term1 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4374008 _103718 _103721 x) (@lem4374007 _103718 _103721 x)). Qed.
Lemma lem4374010 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term2 _103718 _103721 x y.
Proof. exact (@lem4374009 _103718 _103721 x y). Qed.
Lemma lem4374011 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term2 _103718 _103721 x y) = (term3 _103718 _103721 x y).
Proof. exact (eq_refl (term2 _103718 _103721 x y)). Qed.
Lemma lem4374012 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term3 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4374011 _103718 _103721 x y) (@lem4374010 _103718 _103721 x y)). Qed.
Lemma lem4374013 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term4 _103718 _103721 x y s.
Proof. exact (@lem4374012 _103718 _103721 x y s). Qed.
Lemma lem4374014 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term4 _103718 _103721 x y s) = (term5 _103718 _103721 x s y).
Proof. exact (eq_refl (term4 _103718 _103721 x y s)). Qed.
Lemma lem4374015 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term5 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4374014 _103718 _103721 x s y) (@lem4374013 _103718 _103721 x y s)). Qed.
Lemma lem4374016 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term6 _103718 _103721 x s y t.
Proof. exact (@lem4374015 _103718 _103721 x s y t). Qed.
Lemma lem4374017 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term6 _103718 _103721 x s y t) = ((term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term6 _103718 _103721 x s y t)). Qed.
Lemma lem4374043 {_83095 : Type'} : term9 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4374044 {_83095 : Type'} (p : _83095 -> Prop) : term10 _83095 p.
Proof. exact (@lem4374043 _83095 p). Qed.
Lemma lem4374045 {_83095 : Type'} (p : _83095 -> Prop) : (term10 _83095 p) = (term11 _83095 p).
Proof. exact (eq_refl (term10 _83095 p)). Qed.
Lemma lem4374046 {_83095 : Type'} (p : _83095 -> Prop) : term11 _83095 p.
Proof. exact (EQ_MP (@lem4374045 _83095 p) (@lem4374044 _83095 p)). Qed.
Lemma lem4374047 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term12 _83095 p x.
Proof. exact (@lem4374046 _83095 p x). Qed.
Lemma lem4374048 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term12 _83095 p x) = ((term13 _83095 x p) = (p x)).
Proof. exact (eq_refl (term12 _83095 p x)). Qed.
Lemma lem4374057 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term14 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4374058 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = ((term15 _5106 _5107 P) = (term16 _5106 _5107 P)).
Proof. exact (eq_refl (term14 _5106 _5107 P)). Qed.
Lemma lem4374060 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4374061 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem4374062 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem4374061 A s) (@lem4374060 A s)). Qed.
Lemma lem4374063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem4374062 A s t). Qed.
Lemma lem4374064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem4374081 {_89711 _89725 : Type'} : term21 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem4374082 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term22 _89711 _89725 P.
Proof. exact (@lem4374081 _89711 _89725 P). Qed.
Lemma lem4374083 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term22 _89711 _89725 P) = (term23 _89711 _89725 P).
Proof. exact (eq_refl (term22 _89711 _89725 P)). Qed.
Lemma lem4374084 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term23 _89711 _89725 P.
Proof. exact (EQ_MP (@lem4374083 _89711 _89725 P) (@lem4374082 _89711 _89725 P)). Qed.
Lemma lem4374085 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term24 _89711 _89725 P f.
Proof. exact (@lem4374084 _89711 _89725 P f). Qed.
Lemma lem4374086 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term24 _89711 _89725 P f) = ((term25 _89711 _89725 P f) = (term26 _89711 _89725 P f)).
Proof. exact (eq_refl (term24 _89711 _89725 P f)). Qed.
Lemma lem4374104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem4374064 A s t) (@lem4374063 A s t)). Qed.
Lemma lem4374105 {_105011 _105012 : Type'} (s : type1210 _105011 _105012) (t : type1210 _105011 _105012) : (s = t) = (term27 _105011 _105012 s t).
Proof. exact (@lem4374104 (prod _105011 _105012) s t). Qed.
Lemma lem4374106 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term28 _105011 _105012 f t) = (term29 _105011 _105012 f t)) = (term30 _105011 _105012 f t).
Proof. exact (@lem4374105 _105011 _105012 (term28 _105011 _105012 f t) (term29 _105011 _105012 f t)). Qed.
Lemma lem4374112 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = (term16 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4374058 _5106 _5107 P) (@lem4374057 _5106 _5107 P)). Qed.
Lemma lem4374113 {_105011 _105012 : Type'} (P : type1210 _105011 _105012) : (term31 _105011 _105012 P) = (term32 _105011 _105012 P).
Proof. exact (@lem4374112 _105012 _105011 P). Qed.
Lemma lem4374114 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term33 _105011 _105012 f t) = (term34 _105011 _105012 f t).
Proof. exact (@lem4374113 _105011 _105012 (term35 _105011 _105012 f t)). Qed.
Lemma lem4374115 {_105011 _105012 : Type'} (x : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term36 _105011 _105012 f t x) = ((term37 _105011 _105012 x f t) = (term38 _105011 _105012 x f t)).
Proof. exact (eq_refl (term36 _105011 _105012 f t x)). Qed.
Lemma lem4374116 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term39 _105011 _105012 f t) = (term35 _105011 _105012 f t).
Proof. exact (fun_ext (fun x : prod _105011 _105012 => @lem4374115 _105011 _105012 x f t)). Qed.
Lemma lem4374117 {_105011 _105012 : Type'} : (@all (prod _105011 _105012)) = (@all (prod _105011 _105012)).
Proof. exact (eq_refl (@all (prod _105011 _105012))). Qed.
Lemma lem4374118 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term33 _105011 _105012 f t) = (term30 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374117 _105011 _105012) (@lem4374116 _105011 _105012 f t)). Qed.
Lemma lem4374119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374120 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term40 _105011 _105012 f t) = (term41 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374119) (@lem4374118 _105011 _105012 f t)). Qed.
Lemma lem4374121 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term42 _105011 _105012 f t p1 p2) = ((term43 _105011 _105012 p1 p2 f t) = (term44 _105011 _105012 p1 p2 f t)).
Proof. exact (eq_refl (term42 _105011 _105012 f t p1 p2)). Qed.
Lemma lem4374122 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) : (term45 _105011 _105012 f t p1) = (term46 _105011 _105012 p1 f t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4374121 _105011 _105012 p1 p2 f t)). Qed.
Lemma lem4374123 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4374124 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (t : _105012 -> Prop) : (term47 _105011 _105012 f t p1) = (term48 _105011 _105012 p1 f t).
Proof. exact (MK_COMB (@lem4374123 _105012) (@lem4374122 _105011 _105012 p1 f t)). Qed.
Lemma lem4374125 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term49 _105011 _105012 f t) = (term50 _105011 _105012 f t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4374124 _105011 _105012 p1 f t)). Qed.
Lemma lem4374126 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4374127 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term34 _105011 _105012 f t) = (term51 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374126 _105011) (@lem4374125 _105011 _105012 f t)). Qed.
Lemma lem4374128 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term33 _105011 _105012 f t) = (term34 _105011 _105012 f t)) = ((term30 _105011 _105012 f t) = (term51 _105011 _105012 f t)).
Proof. exact (MK_COMB (@lem4374120 _105011 _105012 f t) (@lem4374127 _105011 _105012 f t)). Qed.
Lemma lem4374129 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term30 _105011 _105012 f t) = (term51 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4374128 _105011 _105012 f t) (@lem4374114 _105011 _105012 f t)). Qed.
Lemma lem4374136 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term28 _105011 _105012 f t) = (term29 _105011 _105012 f t)) = (term51 _105011 _105012 f t).
Proof. exact (TRANS (@lem4374106 _105011 _105012 f t) (@lem4374129 _105011 _105012 f t)). Qed.
Lemma lem4374148 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4374017 _103718 _103721 x s y t) (@lem4374016 _103718 _103721 x s y t)). Qed.
Lemma lem4374149 {_105011 _105012 : Type'} (x : _105011) (s : _105011 -> Prop) (y : _105012) (t : _105012 -> Prop) : (term7 _105011 _105012 x y s t) = (term8 _105011 _105012 x s y t).
Proof. exact (@lem4374148 _105011 _105012 x s y t). Qed.
Lemma lem4374150 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (p2 : _105012) (t : _105012 -> Prop) : (term43 _105011 _105012 p1 p2 f t) = (term52 _105011 _105012 p1 f p2 t).
Proof. exact (@lem4374149 _105011 _105012 p1 (@INTERS _105011 f) p2 t). Qed.
Lemma lem4374153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374154 {_105011 _105012 : Type'} (p1 : _105011) (f : type686 _105011) (p2 : _105012) (t : _105012 -> Prop) : (term53 _105011 _105012 p1 p2 f t) = (term54 _105011 _105012 p1 f p2 t).
Proof. exact (MK_COMB (@lem4374153) (@lem4374150 _105011 _105012 p1 f p2 t)). Qed.
Lemma lem4374156 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term25 _89711 _89725 P f) = (term26 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem4374086 _89711 _89725 P f) (@lem4374085 _89711 _89725 P f)). Qed.
Lemma lem4374157 {_105011 _105012 : Type'} (P : type686 _105011) (f : type664 _105011 _105012) : (term55 _105011 _105012 P f) = (term56 _105011 _105012 P f).
Proof. exact (@lem4374156 (prod _105011 _105012) (_105011 -> Prop) P f). Qed.
Lemma lem4374158 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term57 _105011 _105012 f t) = (term58 _105011 _105012 f t).
Proof. exact (@lem4374157 _105011 _105012 (term59 _105011 f) (term60 _105011 _105012 t)). Qed.
Lemma lem4374159 {_105011 : Type'} (s : _105011 -> Prop) (f : type686 _105011) : (term61 _105011 f s) = (@IN (_105011 -> Prop) s f).
Proof. exact (eq_refl (term61 _105011 f s)). Qed.
Lemma lem4374160 {_105011 _105012 : Type'} (GEN_PVAR_138 : type1210 _105011 _105012) : (@SETSPEC ((prod _105011 _105012) -> Prop) GEN_PVAR_138) = (@SETSPEC ((prod _105011 _105012) -> Prop) GEN_PVAR_138).
Proof. exact (eq_refl (@SETSPEC ((prod _105011 _105012) -> Prop) GEN_PVAR_138)). Qed.
Lemma lem4374161 {_105011 _105012 : Type'} (GEN_PVAR_138 : type1210 _105011 _105012) (s : _105011 -> Prop) (f : type686 _105011) : (term62 _105011 _105012 GEN_PVAR_138 f s) = (term63 _105011 _105012 GEN_PVAR_138 s f).
Proof. exact (MK_COMB (@lem4374160 _105011 _105012 GEN_PVAR_138) (@lem4374159 _105011 s f)). Qed.
Lemma lem4374162 {_105011 _105012 : Type'} (s : _105011 -> Prop) (t : _105012 -> Prop) : (term64 _105011 _105012 t s) = (@CROSS _105012 _105011 s t).
Proof. exact (eq_refl (term64 _105011 _105012 t s)). Qed.
Lemma lem4374163 {_105011 _105012 : Type'} (GEN_PVAR_138 : type1210 _105011 _105012) (f : type686 _105011) (s : _105011 -> Prop) (t : _105012 -> Prop) : (term65 _105011 _105012 GEN_PVAR_138 f t s) = (term66 _105011 _105012 GEN_PVAR_138 f s t).
Proof. exact (MK_COMB (@lem4374161 _105011 _105012 GEN_PVAR_138 s f) (@lem4374162 _105011 _105012 s t)). Qed.
Lemma lem4374164 {_105011 _105012 : Type'} (GEN_PVAR_138 : type1210 _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term67 _105011 _105012 GEN_PVAR_138 f t) = (term68 _105011 _105012 GEN_PVAR_138 f t).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4374163 _105011 _105012 GEN_PVAR_138 f s t)). Qed.
Lemma lem4374165 {_105011 : Type'} : (@ex (_105011 -> Prop)) = (@ex (_105011 -> Prop)).
Proof. exact (eq_refl (@ex (_105011 -> Prop))). Qed.
Lemma lem4374166 {_105011 _105012 : Type'} (GEN_PVAR_138 : type1210 _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term69 _105011 _105012 GEN_PVAR_138 f t) = (term70 _105011 _105012 GEN_PVAR_138 f t).
Proof. exact (MK_COMB (@lem4374165 _105011) (@lem4374164 _105011 _105012 GEN_PVAR_138 f t)). Qed.
Lemma lem4374167 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term71 _105011 _105012 f t) = (term72 _105011 _105012 f t).
Proof. exact (fun_ext (fun GEN_PVAR_138 : type1210 _105011 _105012 => @lem4374166 _105011 _105012 GEN_PVAR_138 f t)). Qed.
Lemma lem4374168 {_105011 _105012 : Type'} : (@GSPEC ((prod _105011 _105012) -> Prop)) = (@GSPEC ((prod _105011 _105012) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _105011 _105012) -> Prop))). Qed.
Lemma lem4374169 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term73 _105011 _105012 f t) = (term74 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374168 _105011 _105012) (@lem4374167 _105011 _105012 f t)). Qed.
Lemma lem4374170 {_105011 _105012 : Type'} : (@INTERS (prod _105011 _105012)) = (@INTERS (prod _105011 _105012)).
Proof. exact (eq_refl (@INTERS (prod _105011 _105012))). Qed.
Lemma lem4374171 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term57 _105011 _105012 f t) = (term29 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374170 _105011 _105012) (@lem4374169 _105011 _105012 f t)). Qed.
Lemma lem4374172 {_105011 _105012 : Type'} : (@eq ((prod _105011 _105012) -> Prop)) = (@eq ((prod _105011 _105012) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _105011 _105012) -> Prop))). Qed.
Lemma lem4374173 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term75 _105011 _105012 f t) = (term76 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374172 _105011 _105012) (@lem4374171 _105011 _105012 f t)). Qed.
Lemma lem4374174 {_105011 : Type'} (s : _105011 -> Prop) (f : type686 _105011) : (term61 _105011 f s) = (@IN (_105011 -> Prop) s f).
Proof. exact (eq_refl (term61 _105011 f s)). Qed.
Lemma lem4374175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374176 {_105011 : Type'} (s : _105011 -> Prop) (f : type686 _105011) : (term77 _105011 f s) = (term78 _105011 s f).
Proof. exact (MK_COMB (@lem4374175) (@lem4374174 _105011 s f)). Qed.
Lemma lem4374177 {_105011 _105012 : Type'} (s : _105011 -> Prop) (t : _105012 -> Prop) : (term64 _105011 _105012 t s) = (@CROSS _105012 _105011 s t).
Proof. exact (eq_refl (term64 _105011 _105012 t s)). Qed.
Lemma lem4374178 {_105011 _105012 : Type'} (a : prod _105011 _105012) : (@IN (prod _105011 _105012) a) = (@IN (prod _105011 _105012) a).
Proof. exact (eq_refl (@IN (prod _105011 _105012) a)). Qed.
Lemma lem4374179 {_105011 _105012 : Type'} (a : prod _105011 _105012) (s : _105011 -> Prop) (t : _105012 -> Prop) : (term79 _105011 _105012 a t s) = (term80 _105011 _105012 a s t).
Proof. exact (MK_COMB (@lem4374178 _105011 _105012 a) (@lem4374177 _105011 _105012 s t)). Qed.
Lemma lem4374180 {_105011 _105012 : Type'} (f : type686 _105011) (a : prod _105011 _105012) (s : _105011 -> Prop) (t : _105012 -> Prop) : (term81 _105011 _105012 f a t s) = (term82 _105011 _105012 f a s t).
Proof. exact (MK_COMB (@lem4374176 _105011 s f) (@lem4374179 _105011 _105012 a s t)). Qed.
Lemma lem4374181 {_105011 _105012 : Type'} (f : type686 _105011) (a : prod _105011 _105012) (t : _105012 -> Prop) : (term83 _105011 _105012 f a t) = (term84 _105011 _105012 f a t).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4374180 _105011 _105012 f a s t)). Qed.
Lemma lem4374182 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4374183 {_105011 _105012 : Type'} (f : type686 _105011) (a : prod _105011 _105012) (t : _105012 -> Prop) : (term85 _105011 _105012 f a t) = (term86 _105011 _105012 f a t).
Proof. exact (MK_COMB (@lem4374182 _105011) (@lem4374181 _105011 _105012 f a t)). Qed.
Lemma lem4374184 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) : (@SETSPEC (prod _105011 _105012) GEN_PVAR_56) = (@SETSPEC (prod _105011 _105012) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _105011 _105012) GEN_PVAR_56)). Qed.
Lemma lem4374185 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (a : prod _105011 _105012) (t : _105012 -> Prop) : (term87 _105011 _105012 GEN_PVAR_56 f a t) = (term88 _105011 _105012 GEN_PVAR_56 f a t).
Proof. exact (MK_COMB (@lem4374184 _105011 _105012 GEN_PVAR_56) (@lem4374183 _105011 _105012 f a t)). Qed.
Lemma lem4374186 {_105011 _105012 : Type'} (a : prod _105011 _105012) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4374187 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) (a : prod _105011 _105012) : (term89 _105011 _105012 GEN_PVAR_56 f t a) = (term90 _105011 _105012 GEN_PVAR_56 f t a).
Proof. exact (MK_COMB (@lem4374185 _105011 _105012 GEN_PVAR_56 f a t) (@lem4374186 _105011 _105012 a)). Qed.
Lemma lem4374188 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term91 _105011 _105012 GEN_PVAR_56 f t) = (term92 _105011 _105012 GEN_PVAR_56 f t).
Proof. exact (fun_ext (fun a : prod _105011 _105012 => @lem4374187 _105011 _105012 GEN_PVAR_56 f t a)). Qed.
Lemma lem4374189 {_105011 _105012 : Type'} : (@ex (prod _105011 _105012)) = (@ex (prod _105011 _105012)).
Proof. exact (eq_refl (@ex (prod _105011 _105012))). Qed.
Lemma lem4374190 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term93 _105011 _105012 GEN_PVAR_56 f t) = (term94 _105011 _105012 GEN_PVAR_56 f t).
Proof. exact (MK_COMB (@lem4374189 _105011 _105012) (@lem4374188 _105011 _105012 GEN_PVAR_56 f t)). Qed.
Lemma lem4374191 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term95 _105011 _105012 f t) = (term96 _105011 _105012 f t).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _105011 _105012 => @lem4374190 _105011 _105012 GEN_PVAR_56 f t)). Qed.
Lemma lem4374192 {_105011 _105012 : Type'} : (@GSPEC (prod _105011 _105012)) = (@GSPEC (prod _105011 _105012)).
Proof. exact (eq_refl (@GSPEC (prod _105011 _105012))). Qed.
Lemma lem4374193 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term58 _105011 _105012 f t) = (term97 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374192 _105011 _105012) (@lem4374191 _105011 _105012 f t)). Qed.
Lemma lem4374194 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term57 _105011 _105012 f t) = (term58 _105011 _105012 f t)) = ((term29 _105011 _105012 f t) = (term97 _105011 _105012 f t)).
Proof. exact (MK_COMB (@lem4374173 _105011 _105012 f t) (@lem4374193 _105011 _105012 f t)). Qed.
Lemma lem4374195 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term29 _105011 _105012 f t) = (term97 _105011 _105012 f t).
Proof. exact (EQ_MP (@lem4374194 _105011 _105012 f t) (@lem4374158 _105011 _105012 f t)). Qed.
Lemma lem4374208 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) : (term98 _105011 _105012 p1 p2) = (term98 _105011 _105012 p1 p2).
Proof. exact (eq_refl (term98 _105011 _105012 p1 p2)). Qed.
Lemma lem4374209 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term44 _105011 _105012 p1 p2 f t) = (term99 _105011 _105012 p1 p2 f t).
Proof. exact (MK_COMB (@lem4374208 _105011 _105012 p1 p2) (@lem4374195 _105011 _105012 f t)). Qed.
Lemma lem4374211 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term13 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4374048 _83095 p x) (@lem4374047 _83095 p x)). Qed.
Lemma lem4374212 {_105011 _105012 : Type'} (p : type1210 _105011 _105012) (x : prod _105011 _105012) : (term100 _105011 _105012 x p) = (p x).
Proof. exact (@lem4374211 (prod _105011 _105012) p x). Qed.
Lemma lem4374213 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) (p1 : _105011) (p2 : _105012) : (term101 _105011 _105012 p1 p2 f t) = (term102 _105011 _105012 f t p1 p2).
Proof. exact (@lem4374212 _105011 _105012 (term103 _105011 _105012 f t) (@pair _105011 _105012 p1 p2)). Qed.
Lemma lem4374214 {_105011 _105012 : Type'} (f : type686 _105011) (a : prod _105011 _105012) (t : _105012 -> Prop) : (term104 _105011 _105012 f t a) = (term86 _105011 _105012 f a t).
Proof. exact (eq_refl (term104 _105011 _105012 f t a)). Qed.
Lemma lem4374215 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) : (@SETSPEC (prod _105011 _105012) GEN_PVAR_56) = (@SETSPEC (prod _105011 _105012) GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC (prod _105011 _105012) GEN_PVAR_56)). Qed.
Lemma lem4374216 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (a : prod _105011 _105012) (t : _105012 -> Prop) : (term105 _105011 _105012 GEN_PVAR_56 f t a) = (term88 _105011 _105012 GEN_PVAR_56 f a t).
Proof. exact (MK_COMB (@lem4374215 _105011 _105012 GEN_PVAR_56) (@lem4374214 _105011 _105012 f a t)). Qed.
Lemma lem4374217 {_105011 _105012 : Type'} (a : prod _105011 _105012) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4374218 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) (a : prod _105011 _105012) : (term106 _105011 _105012 GEN_PVAR_56 f t a) = (term90 _105011 _105012 GEN_PVAR_56 f t a).
Proof. exact (MK_COMB (@lem4374216 _105011 _105012 GEN_PVAR_56 f a t) (@lem4374217 _105011 _105012 a)). Qed.
Lemma lem4374219 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term107 _105011 _105012 GEN_PVAR_56 f t) = (term92 _105011 _105012 GEN_PVAR_56 f t).
Proof. exact (fun_ext (fun a : prod _105011 _105012 => @lem4374218 _105011 _105012 GEN_PVAR_56 f t a)). Qed.
Lemma lem4374220 {_105011 _105012 : Type'} : (@ex (prod _105011 _105012)) = (@ex (prod _105011 _105012)).
Proof. exact (eq_refl (@ex (prod _105011 _105012))). Qed.
Lemma lem4374221 {_105011 _105012 : Type'} (GEN_PVAR_56 : prod _105011 _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term108 _105011 _105012 GEN_PVAR_56 f t) = (term94 _105011 _105012 GEN_PVAR_56 f t).
Proof. exact (MK_COMB (@lem4374220 _105011 _105012) (@lem4374219 _105011 _105012 GEN_PVAR_56 f t)). Qed.
Lemma lem4374222 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term109 _105011 _105012 f t) = (term96 _105011 _105012 f t).
Proof. exact (fun_ext (fun GEN_PVAR_56 : prod _105011 _105012 => @lem4374221 _105011 _105012 GEN_PVAR_56 f t)). Qed.
Lemma lem4374223 {_105011 _105012 : Type'} : (@GSPEC (prod _105011 _105012)) = (@GSPEC (prod _105011 _105012)).
Proof. exact (eq_refl (@GSPEC (prod _105011 _105012))). Qed.
Lemma lem4374224 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term110 _105011 _105012 f t) = (term97 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374223 _105011 _105012) (@lem4374222 _105011 _105012 f t)). Qed.
Lemma lem4374225 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) : (term98 _105011 _105012 p1 p2) = (term98 _105011 _105012 p1 p2).
Proof. exact (eq_refl (term98 _105011 _105012 p1 p2)). Qed.
Lemma lem4374226 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term101 _105011 _105012 p1 p2 f t) = (term99 _105011 _105012 p1 p2 f t).
Proof. exact (MK_COMB (@lem4374225 _105011 _105012 p1 p2) (@lem4374224 _105011 _105012 f t)). Qed.
Lemma lem4374227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374228 {_105011 _105012 : Type'} (p1 : _105011) (p2 : _105012) (f : type686 _105011) (t : _105012 -> Prop) : (term111 _105011 _105012 p1 p2 f t) = (term112 _105011 _105012 p1 p2 f t).
Proof. exact (MK_COMB (@lem4374227) (@lem4374226 _105011 _105012 p1 p2 f t)). Qed.
Lemma lem4374229 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term102 _105011 _105012 f t p1 p2) = (term113 _105011 _105012 f p1 p2 t).
Proof. exact (eq_refl (term102 _105011 _105012 f t p1 p2)). Qed.
Lemma lem4374230 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : ((term101 _105011 _105012 p1 p2 f t) = (term102 _105011 _105012 f t p1 p2)) = ((term99 _105011 _105012 p1 p2 f t) = (term113 _105011 _105012 f p1 p2 t)).
Proof. exact (MK_COMB (@lem4374228 _105011 _105012 p1 p2 f t) (@lem4374229 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374231 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term99 _105011 _105012 p1 p2 f t) = (term113 _105011 _105012 f p1 p2 t).
Proof. exact (EQ_MP (@lem4374230 _105011 _105012 f p1 p2 t) (@lem4374213 _105011 _105012 f t p1 p2)). Qed.
Lemma lem4374241 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term7 _103718 _103721 x y s t) = (term8 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4374017 _103718 _103721 x s y t) (@lem4374016 _103718 _103721 x s y t)). Qed.
Lemma lem4374242 {_105011 _105012 : Type'} (x : _105011) (s : _105011 -> Prop) (y : _105012) (t : _105012 -> Prop) : (term7 _105011 _105012 x y s t) = (term8 _105011 _105012 x s y t).
Proof. exact (@lem4374241 _105011 _105012 x s y t). Qed.
Lemma lem4374243 {_105011 _105012 : Type'} (p1 : _105011) (s : _105011 -> Prop) (p2 : _105012) (t : _105012 -> Prop) : (term7 _105011 _105012 p1 p2 s t) = (term8 _105011 _105012 p1 s p2 t).
Proof. exact (@lem4374242 _105011 _105012 p1 s p2 t). Qed.
Lemma lem4374246 {_105011 : Type'} (s : _105011 -> Prop) (f : type686 _105011) : (term78 _105011 s f) = (term78 _105011 s f).
Proof. exact (eq_refl (term78 _105011 s f)). Qed.
Lemma lem4374247 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (s : _105011 -> Prop) (p2 : _105012) (t : _105012 -> Prop) : (term114 _105011 _105012 f p1 p2 s t) = (term115 _105011 _105012 f p1 s p2 t).
Proof. exact (MK_COMB (@lem4374246 _105011 s f) (@lem4374243 _105011 _105012 p1 s p2 t)). Qed.
Lemma lem4374250 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term116 _105011 _105012 f p1 p2 t) = (term117 _105011 _105012 f p1 p2 t).
Proof. exact (fun_ext (fun s : _105011 -> Prop => @lem4374247 _105011 _105012 f p1 s p2 t)). Qed.
Lemma lem4374251 {_105011 : Type'} : (@all (_105011 -> Prop)) = (@all (_105011 -> Prop)).
Proof. exact (eq_refl (@all (_105011 -> Prop))). Qed.
Lemma lem4374252 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term113 _105011 _105012 f p1 p2 t) = (term118 _105011 _105012 f p1 p2 t).
Proof. exact (MK_COMB (@lem4374251 _105011) (@lem4374250 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374259 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term99 _105011 _105012 p1 p2 f t) = (term118 _105011 _105012 f p1 p2 t).
Proof. exact (TRANS (@lem4374231 _105011 _105012 f p1 p2 t) (@lem4374252 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374260 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : (term44 _105011 _105012 p1 p2 f t) = (term118 _105011 _105012 f p1 p2 t).
Proof. exact (TRANS (@lem4374209 _105011 _105012 p1 p2 f t) (@lem4374259 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374261 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (p2 : _105012) (t : _105012 -> Prop) : ((term43 _105011 _105012 p1 p2 f t) = (term44 _105011 _105012 p1 p2 f t)) = ((term52 _105011 _105012 p1 f p2 t) = (term118 _105011 _105012 f p1 p2 t)).
Proof. exact (MK_COMB (@lem4374154 _105011 _105012 p1 f p2 t) (@lem4374260 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374266 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term46 _105011 _105012 p1 f t) = (term119 _105011 _105012 f p1 t).
Proof. exact (fun_ext (fun p2 : _105012 => @lem4374261 _105011 _105012 f p1 p2 t)). Qed.
Lemma lem4374267 {_105012 : Type'} : (@all _105012) = (@all _105012).
Proof. exact (eq_refl (@all _105012)). Qed.
Lemma lem4374268 {_105011 _105012 : Type'} (f : type686 _105011) (p1 : _105011) (t : _105012 -> Prop) : (term48 _105011 _105012 p1 f t) = (term120 _105011 _105012 f p1 t).
Proof. exact (MK_COMB (@lem4374267 _105012) (@lem4374266 _105011 _105012 f p1 t)). Qed.
Lemma lem4374275 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term50 _105011 _105012 f t) = (term121 _105011 _105012 f t).
Proof. exact (fun_ext (fun p1 : _105011 => @lem4374268 _105011 _105012 f p1 t)). Qed.
Lemma lem4374276 {_105011 : Type'} : (@all _105011) = (@all _105011).
Proof. exact (eq_refl (@all _105011)). Qed.
Lemma lem4374277 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term51 _105011 _105012 f t) = (term122 _105011 _105012 f t).
Proof. exact (MK_COMB (@lem4374276 _105011) (@lem4374275 _105011 _105012 f t)). Qed.
Lemma lem4374284 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : ((term28 _105011 _105012 f t) = (term29 _105011 _105012 f t)) = (term122 _105011 _105012 f t).
Proof. exact (TRANS (@lem4374136 _105011 _105012 f t) (@lem4374277 _105011 _105012 f t)). Qed.
Lemma lem4374285 {_105011 _105012 : Type'} (f : type686 _105011) (t : _105012 -> Prop) : (term122 _105011 _105012 f t) = ((term28 _105011 _105012 f t) = (term29 _105011 _105012 f t)).
Proof. exact (SYM (@lem4374284 _105011 _105012 f t)). Qed.
