Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_BIJECTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EQ_TRANS_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import ITERATE_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18897_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem5942956 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5942957 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5942958 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5942957 t1) (@lem5942956 t1)). Qed.
Lemma lem5942959 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5942958 t1 t2). Qed.
Lemma lem5942960 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5942961 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5942960 t1 t2) (@lem5942959 t1 t2)). Qed.
Lemma lem5942962 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5942961 t1 t2 t3). Qed.
Lemma lem5942963 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5942964 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5942963 t1 t2 t3) (@lem5942962 t1 t2 t3)). Qed.
Lemma lem5942965 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5942964 t1 t2 t3)). Qed.
Lemma lem5942966 {A C : Type'} : term7 A C.
Proof. exact (@lem5942955 A A C). Qed.
Lemma lem5942967 {A C : Type'} (op : type1400 C) : term8 A C op.
Proof. exact (@lem5942966 A C op). Qed.
Lemma lem5942968 {A C : Type'} (op : type1400 C) : (term8 A C op) = (term9 A C op).
Proof. exact (eq_refl (term8 A C op)). Qed.
Lemma lem5942970 {A B : Type'} (y : B) : term10 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem5942971 {A B : Type'} (y : B) : (term10 A B y) = (term11 A B y).
Proof. exact (eq_refl (term10 A B y)). Qed.
Lemma lem5942972 {A B : Type'} (y : B) : term11 A B y.
Proof. exact (EQ_MP (@lem5942971 A B y) (@lem5942970 A B y)). Qed.
Lemma lem5942973 {A B : Type'} (y : B) (s : A -> Prop) : term12 A B y s.
Proof. exact (@lem5942972 A B y s). Qed.
Lemma lem5942974 {A B : Type'} (y : B) (s : A -> Prop) : (term12 A B y s) = (term13 A B y s).
Proof. exact (eq_refl (term12 A B y s)). Qed.
Lemma lem5942975 {A B : Type'} (y : B) (s : A -> Prop) : term13 A B y s.
Proof. exact (EQ_MP (@lem5942974 A B y s) (@lem5942973 A B y s)). Qed.
Lemma lem5942976 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term14 A B y s f.
Proof. exact (@lem5942975 A B y s f). Qed.
Lemma lem5942977 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term14 A B y s f) = ((term15 A B y f s) = (term16 A B y f s)).
Proof. exact (eq_refl (term14 A B y s f)). Qed.
Lemma lem5942979 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem5942980 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem5942981 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem5942980 A s) (@lem5942979 A s)). Qed.
Lemma lem5942982 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem5942981 A s t). Qed.
Lemma lem5942983 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem5942985 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem5942986 {A : Type'} (x : A) (h1 : term21 A) : term22 A x.
Proof. exact (@lem5942985 A h1 x). Qed.
Lemma lem5942987 {A : Type'} (x : A) : (term22 A x) = (term23 A x).
Proof. exact (eq_refl (term22 A x)). Qed.
Lemma lem5942988 {A : Type'} (x : A) (h1 : term21 A) : term23 A x.
Proof. exact (EQ_MP (@lem5942987 A x) (@lem5942986 A x h1)). Qed.
Lemma lem5942989 {A : Type'} (x : A) (y : A) (h1 : term21 A) : term24 A x y.
Proof. exact (@lem5942988 A x h1 y). Qed.
Lemma lem5942990 {A : Type'} (y : A) (x : A) : (term24 A x y) = (term25 A y x).
Proof. exact (eq_refl (term24 A x y)). Qed.
Lemma lem5942991 {A : Type'} (y : A) (x : A) (h1 : term21 A) : term25 A y x.
Proof. exact (EQ_MP (@lem5942990 A y x) (@lem5942989 A x y h1)). Qed.
Lemma lem5942992 {A : Type'} (y : A) (x : A) (z : A) (h1 : term21 A) : term26 A y x z.
Proof. exact (@lem5942991 A y x h1 z). Qed.
Lemma lem5942993 {A : Type'} (y : A) (x : A) (z : A) : (term26 A y x z) = (term27 A y x z).
Proof. exact (eq_refl (term26 A y x z)). Qed.
Lemma lem5942994 {A : Type'} (y : A) (x : A) (z : A) (h1 : term21 A) : term27 A y x z.
Proof. exact (EQ_MP (@lem5942993 A y x z) (@lem5942992 A y x z h1)). Qed.
Lemma lem5942995 {A : Type'} (x : A) (y : A) (z : A) (h1 : term28 A x y z) : term28 A x y z.
Proof. exact (h1). Qed.
Lemma lem5942996 {A : Type'} (x : A) (y : A) (z : A) (h1 : term21 A) (h2 : term28 A x y z) : x = z.
Proof. exact (@lem5942994 A y x z h1 (@lem5942995 A x y z h2)). Qed.
Lemma lem5942997 {A : Type'} (x : A) (y : A) (z : A) (h1 : term28 A x y z) : term29 A x z.
Proof. exact (fun h0 : term21 A => @lem5942996 A x y z h0 h1). Qed.
Lemma lem5942998 {A : Type'} (x : A) (z : A) (h1 : term30 A x z) : term30 A x z.
Proof. exact (h1). Qed.
Lemma lem5942999 {A : Type'} (x : A) (z : A) (h1 : term30 A x z) : term29 A x z.
Proof. exact (ex_elim (@lem5942998 A x z h1) (fun y : A => fun h0 : term31 A x z y => @lem5942997 A x y z h0)). Qed.
Lemma lem5943000 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem5943001 {A : Type'} (x : A) (z : A) (h1 : term21 A) (h2 : term30 A x z) : x = z.
Proof. exact (@lem5942999 A x z h2 (@lem5943000 A h1)). Qed.
Lemma lem5943002 {A : Type'} (x : A) (z : A) (h1 : term21 A) : term32 A x z.
Proof. exact (fun h0 : term30 A x z => @lem5943001 A x z h1 h0). Qed.
Lemma lem5943003 {A : Type'} (x : A) (h1 : term21 A) : term33 A x.
Proof. exact (fun z : A => @lem5943002 A x z h1). Qed.
Lemma lem5943004 {A : Type'} (h1 : term21 A) : term34 A.
Proof. exact (fun x : A => @lem5943003 A x h1). Qed.
Lemma lem5943005 {A : Type'} : term35 A.
Proof. exact (fun h0 : term21 A => @lem5943004 A h0). Qed.
Lemma lem5943006 {A : Type'} : term34 A.
Proof. exact (@lem5943005 A (@lem403 A)). Qed.
Lemma lem5943007 {A : Type'} (x : A) : term36 A x.
Proof. exact (@lem5943006 A x). Qed.
Lemma lem5943008 {A : Type'} (x : A) : (term36 A x) = (term33 A x).
Proof. exact (eq_refl (term36 A x)). Qed.
Lemma lem5943009 {A : Type'} (x : A) : term33 A x.
Proof. exact (EQ_MP (@lem5943008 A x) (@lem5943007 A x)). Qed.
Lemma lem5943010 {A : Type'} (x : A) (z : A) : term37 A x z.
Proof. exact (@lem5943009 A x z). Qed.
Lemma lem5943011 {A : Type'} (x : A) (z : A) : (term37 A x z) = (term32 A x z).
Proof. exact (eq_refl (term37 A x z)). Qed.
Lemma lem5943013 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5943014 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term38 A s p) : term38 A s p.
Proof. exact (h1). Qed.
Lemma lem5943015 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) : term39 A s p.
Proof. exact (h1). Qed.
Lemma lem5943016 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term40 A p s.
Proof. exact (h1). Qed.
Lemma lem5943018 {A : Type'} (x : A) (z : A) : term32 A x z.
Proof. exact (EQ_MP (@lem5943011 A x z) (@lem5943010 A x z)). Qed.
Lemma lem5943019 {B : Type'} (x : B) (z : B) : term32 B x z.
Proof. exact (@lem5943018 B x z). Qed.
Lemma lem5943020 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) (p : A -> A) : term41 A B op s f p.
Proof. exact (@lem5943019 B (@iterate B A op s f) (term42 A B op s f p)). Qed.
Lemma lem5943021 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5943022 {A B : Type'} (op : type1400 B) : (@iterate B A op) = (@iterate B A op).
Proof. exact (eq_refl (@iterate B A op)). Qed.
Lemma lem5943026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem5942983 A s t) (@lem5942982 A s t)). Qed.
Lemma lem5943027 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem5943026 A s t). Qed.
Lemma lem5943028 {A : Type'} (p : A -> A) (s : A -> Prop) : (s = (@IMAGE A A p s)) = (term43 A p s).
Proof. exact (@lem5943027 A s (@IMAGE A A p s)). Qed.
Lemma lem5943038 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term15 A B y f s) = (term16 A B y f s).
Proof. exact (EQ_MP (@lem5942977 A B y f s) (@lem5942976 A B y s f)). Qed.
Lemma lem5943039 {A : Type'} (y : A) (f : A -> A) (s : A -> Prop) : (term44 A y f s) = (term45 A y f s).
Proof. exact (@lem5943038 A A y f s). Qed.
Lemma lem5943040 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term44 A x p s) = (term45 A x p s).
Proof. exact (@lem5943039 A x p s). Qed.
Lemma lem5943051 {A : Type'} (x : A) (s : A -> Prop) : (term46 A x s) = (term46 A x s).
Proof. exact (eq_refl (term46 A x s)). Qed.
Lemma lem5943052 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : ((@IN A x s) = (term44 A x p s)) = ((@IN A x s) = (term45 A x p s)).
Proof. exact (MK_COMB (@lem5943051 A x s) (@lem5943040 A x p s)). Qed.
Lemma lem5943057 {A : Type'} (p : A -> A) (s : A -> Prop) : (term47 A p s) = (term48 A p s).
Proof. exact (fun_ext (fun x : A => @lem5943052 A x p s)). Qed.
Lemma lem5943058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943059 {A : Type'} (p : A -> A) (s : A -> Prop) : (term43 A p s) = (term49 A p s).
Proof. exact (MK_COMB (@lem5943058 A) (@lem5943057 A p s)). Qed.
Lemma lem5943064 {A : Type'} (p : A -> A) (s : A -> Prop) : (s = (@IMAGE A A p s)) = (term49 A p s).
Proof. exact (TRANS (@lem5943028 A p s) (@lem5943059 A p s)). Qed.
Lemma lem5943065 {A : Type'} (p : A -> A) (s : A -> Prop) : (term49 A p s) = (s = (@IMAGE A A p s)).
Proof. exact (SYM (@lem5943064 A p s)). Qed.
Lemma lem5943071 {A C : Type'} (op : type1400 C) : term9 A C op.
Proof. exact (EQ_MP (@lem5942968 A C op) (@lem5942967 A C op)). Qed.
Lemma lem5943072 {A B : Type'} (op : type1400 B) : term9 A B op.
Proof. exact (@lem5943071 A B op). Qed.
Lemma lem5943073 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term50 A B op.
Proof. exact (@lem5943072 A B op (@lem5943013 B op h1)). Qed.
Lemma lem5943074 {A B : Type'} (op : type1400 B) (h1 : term50 A B op) : term50 A B op.
Proof. exact (h1). Qed.
Lemma lem5943075 {A B : Type'} (f : A -> A) (op : type1400 B) (h1 : term50 A B op) : term51 A B op f.
Proof. exact (@lem5943074 A B op h1 f). Qed.
Lemma lem5943076 {A B : Type'} (op : type1400 B) (f : A -> A) : (term51 A B op f) = (term52 A B op f).
Proof. exact (eq_refl (term51 A B op f)). Qed.
Lemma lem5943077 {A B : Type'} (f : A -> A) (op : type1400 B) (h1 : term50 A B op) : term52 A B op f.
Proof. exact (EQ_MP (@lem5943076 A B op f) (@lem5943075 A B f op h1)). Qed.
Lemma lem5943078 {A B : Type'} (f : A -> A) (g : A -> B) (op : type1400 B) (h1 : term50 A B op) : term53 A B op f g.
Proof. exact (@lem5943077 A B f op h1 g). Qed.
Lemma lem5943079 {A B : Type'} (op : type1400 B) (g : A -> B) (f : A -> A) : (term53 A B op f g) = (term54 A B op g f).
Proof. exact (eq_refl (term53 A B op f g)). Qed.
Lemma lem5943080 {A B : Type'} (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : term50 A B op) : term54 A B op g f.
Proof. exact (EQ_MP (@lem5943079 A B op g f) (@lem5943078 A B f g op h1)). Qed.
Lemma lem5943081 {A B : Type'} (g : A -> B) (f : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term50 A B op) : term55 A B op g f s.
Proof. exact (@lem5943080 A B g f op h1 s). Qed.
Lemma lem5943082 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) (f : A -> A) : (term55 A B op g f s) = (term56 A B op s g f).
Proof. exact (eq_refl (term55 A B op g f s)). Qed.
Lemma lem5943083 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : term50 A B op) : term56 A B op s g f.
Proof. exact (EQ_MP (@lem5943082 A B op s g f) (@lem5943081 A B g f s op h1)). Qed.
Lemma lem5943084 {A : Type'} (s : A -> Prop) (f : A -> A) (h1 : term57 A s f) : term57 A s f.
Proof. exact (h1). Qed.
Lemma lem5943085 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> A) (op : type1400 B) (h1 : term57 A s f) (h2 : term50 A B op) : (term58 A B op f s g) = (term42 A B op s g f).
Proof. exact (@lem5943083 A B s g f op h2 (@lem5943084 A s f h1)). Qed.
Lemma lem5943086 {A B : Type'} (op : type1400 B) (g : A -> B) (s : A -> Prop) (f : A -> A) (h1 : term57 A s f) : term59 A B op s g f.
Proof. exact (fun h0 : term50 A B op => @lem5943085 A B g s f op h1 h0). Qed.
Lemma lem5943087 {A B : Type'} (op : type1400 B) (h1 : term50 A B op) : term50 A B op.
Proof. exact (h1). Qed.
Lemma lem5943088 {A B : Type'} (g : A -> B) (s : A -> Prop) (f : A -> A) (op : type1400 B) (h1 : term57 A s f) (h2 : term50 A B op) : (term58 A B op f s g) = (term42 A B op s g f).
Proof. exact (@lem5943086 A B op g s f h1 (@lem5943087 A B op h2)). Qed.
Lemma lem5943089 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : term50 A B op) : term56 A B op s g f.
Proof. exact (fun h0 : term57 A s f => @lem5943088 A B g s f op h0 h1). Qed.
Lemma lem5943090 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : term50 A B op) : term60 A B op s g.
Proof. exact (fun f : A -> A => @lem5943089 A B s g f op h1). Qed.
Lemma lem5943091 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : term50 A B op) : term61 A B op s.
Proof. exact (fun g : A -> B => @lem5943090 A B s g op h1). Qed.
Lemma lem5943092 {A B : Type'} (op : type1400 B) (h1 : term50 A B op) : term62 A B op.
Proof. exact (fun s : A -> Prop => @lem5943091 A B s op h1). Qed.
Lemma lem5943093 {A B : Type'} (op : type1400 B) : term63 A B op.
Proof. exact (fun h0 : term50 A B op => @lem5943092 A B op h0). Qed.
Lemma lem5943094 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term62 A B op.
Proof. exact (@lem5943093 A B op (@lem5943073 A B op h1)). Qed.
Lemma lem5943095 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term64 A B op s.
Proof. exact (@lem5943094 A B op h1 s). Qed.
Lemma lem5943096 {A B : Type'} (op : type1400 B) (s : A -> Prop) : (term64 A B op s) = (term61 A B op s).
Proof. exact (eq_refl (term64 A B op s)). Qed.
Lemma lem5943097 {A B : Type'} (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term61 A B op s.
Proof. exact (EQ_MP (@lem5943096 A B op s) (@lem5943095 A B s op h1)). Qed.
Lemma lem5943098 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term65 A B op s g.
Proof. exact (@lem5943097 A B s op h1 g). Qed.
Lemma lem5943099 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) : (term65 A B op s g) = (term60 A B op s g).
Proof. exact (eq_refl (term65 A B op s g)). Qed.
Lemma lem5943100 {A B : Type'} (s : A -> Prop) (g : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term60 A B op s g.
Proof. exact (EQ_MP (@lem5943099 A B op s g) (@lem5943098 A B s g op h1)). Qed.
Lemma lem5943101 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term66 A B op s g f.
Proof. exact (@lem5943100 A B s g op h1 f). Qed.
Lemma lem5943102 {A B : Type'} (op : type1400 B) (s : A -> Prop) (g : A -> B) (f : A -> A) : (term66 A B op s g f) = (term56 A B op s g f).
Proof. exact (eq_refl (term66 A B op s g f)). Qed.
Lemma lem5943105 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term56 A B op s g f.
Proof. exact (EQ_MP (@lem5943102 A B op s g f) (@lem5943101 A B s g f op h1)). Qed.
Lemma lem5943106 {A B : Type'} (s : A -> Prop) (g : A -> B) (f : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term56 A B op s g f.
Proof. exact (@lem5943105 A B s g f op h1). Qed.
Lemma lem5943107 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term56 A B op s f p.
Proof. exact (@lem5943106 A B s f p op h1). Qed.
Lemma lem5943109 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5943110 {A : Type'} (p : A -> A) (s : A -> Prop) : (term49 A p s) = (term68 A p s).
Proof. exact (@lem5943109 (term49 A p s)). Qed.
Lemma lem5943111 {A : Type'} (p : A -> A) (s : A -> Prop) : (term68 A p s) = (term49 A p s).
Proof. exact (SYM (@lem5943110 A p s)). Qed.
Lemma lem5943112 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term69 A p s) : term69 A p s.
Proof. exact (h1). Qed.
Lemma lem5943115 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term70 A B op p s) : term70 A B op p s.
Proof. exact (h1). Qed.
Lemma lem5943116 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term71 A B op p s.
Proof. exact (fun h0 : term70 A B op p s => @lem5943115 A B op p s h0). Qed.
Lemma lem5943117 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term71 A B op p s) : term71 A B op p s.
Proof. exact (h1). Qed.
Lemma lem5943118 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term70 A B op p s) : term70 A B op p s.
Proof. exact (h1). Qed.
Lemma lem5943119 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term70 A B op p s) (h2 : term71 A B op p s) : term70 A B op p s.
Proof. exact (@lem5943117 A B op p s h2 (@lem5943118 A B op p s h1)). Qed.
Lemma lem5943120 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term70 A B op p s) : term72 A B op p s.
Proof. exact (fun h0 : term71 A B op p s => @lem5943119 A B op p s h1 h0). Qed.
Lemma lem5943121 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term71 A B op p s) : term71 A B op p s.
Proof. exact (h1). Qed.
Lemma lem5943122 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term70 A B op p s) (h2 : term71 A B op p s) : term70 A B op p s.
Proof. exact (@lem5943120 A B op p s h1 (@lem5943121 A B op p s h2)). Qed.
Lemma lem5943123 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term71 A B op p s) : term71 A B op p s.
Proof. exact (fun h0 : term70 A B op p s => @lem5943122 A B op p s h0 h1). Qed.
Lemma lem5943124 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term73 A B op p s.
Proof. exact (fun h0 : term71 A B op p s => @lem5943123 A B op p s h0). Qed.
Lemma lem5943127 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term71 A B op p s.
Proof. exact (@lem5943124 A B op p s (@lem5943116 A B op p s)). Qed.
Lemma lem5943128 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term71 A B op p s.
Proof. exact (@lem5943127 A B op p s). Qed.
Lemma lem5943162 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5943163 {A : Type'} (p : A -> A) (s : A -> Prop) : (term68 A p s) = (term74 A p s).
Proof. exact (@lem5943162 (term69 A p s)). Qed.
Lemma lem5943165 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5943166 {A : Type'} (p : A -> A) (s : A -> Prop) : (term74 A p s) = (term49 A p s).
Proof. exact (@lem5943165 (term49 A p s)). Qed.
Lemma lem5943171 {A : Type'} (p : A -> A) (s : A -> Prop) : (term68 A p s) = (term49 A p s).
Proof. exact (TRANS (@lem5943163 A p s) (@lem5943166 A p s)). Qed.
Lemma lem5943222 {A : Type'} (s : A -> Prop) (p : A -> A) : (term76 A s p) = (term76 A s p).
Proof. exact (eq_refl (term76 A s p)). Qed.
Lemma lem5943223 {A : Type'} (p : A -> A) (s : A -> Prop) : (term77 A p s) = (term78 A p s).
Proof. exact (MK_COMB (@lem5943222 A s p) (@lem5943171 A p s)). Qed.
Lemma lem5943226 {A : Type'} (p : A -> A) (s : A -> Prop) : (term79 A p s) = (term79 A p s).
Proof. exact (eq_refl (term79 A p s)). Qed.
Lemma lem5943227 {A : Type'} (p : A -> A) (s : A -> Prop) : (term80 A p s) = (term81 A p s).
Proof. exact (MK_COMB (@lem5943226 A p s) (@lem5943223 A p s)). Qed.
Lemma lem5943230 {B : Type'} (op : type1400 B) : (term82 B op) = (term82 B op).
Proof. exact (eq_refl (term82 B op)). Qed.
Lemma lem5943231 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : (term70 A B op p s) = (term83 A B op p s).
Proof. exact (MK_COMB (@lem5943230 B op) (@lem5943227 A p s)). Qed.
Lemma lem5943234 {A B : Type'} (p : A -> A) (s : A -> Prop) : (term84 A B p s) = (term85 A B p s).
Proof. exact (fun_ext (fun op : type1400 B => @lem5943231 A B op p s)). Qed.
Lemma lem5943235 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5943236 {A B : Type'} (p : A -> A) (s : A -> Prop) : (term86 A B p s) = (term87 A B p s).
Proof. exact (MK_COMB (@lem5943235 B) (@lem5943234 A B p s)). Qed.
Lemma lem5943241 {A B : Type'} (s : A -> Prop) : (term88 A B s) = (term89 A B s).
Proof. exact (fun_ext (fun p : A -> A => @lem5943236 A B p s)). Qed.
Lemma lem5943242 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5943243 {A B : Type'} (s : A -> Prop) : (term90 A B s) = (term91 A B s).
Proof. exact (MK_COMB (@lem5943242 A) (@lem5943241 A B s)). Qed.
Lemma lem5943248 {A B : Type'} : (term92 A B) = (term93 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5943243 A B s)). Qed.
Lemma lem5943249 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5943258 {A B : Type'} : (term94 A B) = (term95 A B).
Proof. exact (MK_COMB (@lem5943249 A) (@lem5943248 A B)). Qed.
Lemma lem5943263 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term96 A x p x' s) = (term96 A x p x' s).
Proof. exact (eq_refl (term96 A x p x' s)). Qed.
Lemma lem5943264 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term97 A x p s) = (term97 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5943263 A x p x' s)). Qed.
Lemma lem5943265 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943266 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term45 A x p s) = (term45 A x p s).
Proof. exact (MK_COMB (@lem5943265 A) (@lem5943264 A x p s)). Qed.
Lemma lem5943269 {A : Type'} (x : A) (s : A -> Prop) : (term46 A x s) = (term46 A x s).
Proof. exact (eq_refl (term46 A x s)). Qed.
Lemma lem5943270 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : ((@IN A x s) = (term45 A x p s)) = ((@IN A x s) = (term45 A x p s)).
Proof. exact (MK_COMB (@lem5943269 A x s) (@lem5943266 A x p s)). Qed.
Lemma lem5943271 {A : Type'} (p : A -> A) (s : A -> Prop) : (term48 A p s) = (term48 A p s).
Proof. exact (fun_ext (fun x : A => @lem5943270 A x p s)). Qed.
Lemma lem5943272 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943273 {A : Type'} (p : A -> A) (s : A -> Prop) : (term49 A p s) = (term49 A p s).
Proof. exact (MK_COMB (@lem5943272 A) (@lem5943271 A p s)). Qed.
Lemma lem5943278 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term98 A s p x y) = (term98 A s p x y).
Proof. exact (eq_refl (term98 A s p x y)). Qed.
Lemma lem5943279 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term99 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943278 A s p x y)). Qed.
Lemma lem5943280 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5943281 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term100 A s p y).
Proof. exact (MK_COMB (@lem5943280 A) (@lem5943279 A s p y)). Qed.
Lemma lem5943284 {A : Type'} (y : A) (s : A -> Prop) : (term101 A y s) = (term101 A y s).
Proof. exact (eq_refl (term101 A y s)). Qed.
Lemma lem5943285 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term102 A s p y).
Proof. exact (MK_COMB (@lem5943284 A y s) (@lem5943281 A s p y)). Qed.
Lemma lem5943286 {A : Type'} (s : A -> Prop) (p : A -> A) : (term103 A s p) = (term103 A s p).
Proof. exact (fun_ext (fun y : A => @lem5943285 A s p y)). Qed.
Lemma lem5943287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943288 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term39 A s p).
Proof. exact (MK_COMB (@lem5943287 A) (@lem5943286 A s p)). Qed.
Lemma lem5943289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5943290 {A : Type'} (s : A -> Prop) (p : A -> A) : (term76 A s p) = (term76 A s p).
Proof. exact (MK_COMB (@lem5943289) (@lem5943288 A s p)). Qed.
Lemma lem5943291 {A : Type'} (p : A -> A) (s : A -> Prop) : (term78 A p s) = (term78 A p s).
Proof. exact (MK_COMB (@lem5943290 A s p) (@lem5943273 A p s)). Qed.
Lemma lem5943296 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term104 A p x s) = (term104 A p x s).
Proof. exact (eq_refl (term104 A p x s)). Qed.
Lemma lem5943297 {A : Type'} (p : A -> A) (s : A -> Prop) : (term105 A p s) = (term105 A p s).
Proof. exact (fun_ext (fun x : A => @lem5943296 A p x s)). Qed.
Lemma lem5943298 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943299 {A : Type'} (p : A -> A) (s : A -> Prop) : (term40 A p s) = (term40 A p s).
Proof. exact (MK_COMB (@lem5943298 A) (@lem5943297 A p s)). Qed.
Lemma lem5943300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5943301 {A : Type'} (p : A -> A) (s : A -> Prop) : (term79 A p s) = (term79 A p s).
Proof. exact (MK_COMB (@lem5943300) (@lem5943299 A p s)). Qed.
Lemma lem5943302 {A : Type'} (p : A -> A) (s : A -> Prop) : (term81 A p s) = (term81 A p s).
Proof. exact (MK_COMB (@lem5943301 A p s) (@lem5943291 A p s)). Qed.
Lemma lem5943305 {B : Type'} (op : type1400 B) : (term82 B op) = (term82 B op).
Proof. exact (eq_refl (term82 B op)). Qed.
Lemma lem5943306 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : (term83 A B op p s) = (term83 A B op p s).
Proof. exact (MK_COMB (@lem5943305 B op) (@lem5943302 A p s)). Qed.
Lemma lem5943307 {A B : Type'} (p : A -> A) (s : A -> Prop) : (term85 A B p s) = (term85 A B p s).
Proof. exact (fun_ext (fun op : type1400 B => @lem5943306 A B op p s)). Qed.
Lemma lem5943308 {B : Type'} : (@all (B -> B -> B)) = (@all (B -> B -> B)).
Proof. exact (eq_refl (@all (B -> B -> B))). Qed.
Lemma lem5943309 {A B : Type'} (p : A -> A) (s : A -> Prop) : (term87 A B p s) = (term87 A B p s).
Proof. exact (MK_COMB (@lem5943308 B) (@lem5943307 A B p s)). Qed.
Lemma lem5943310 {A B : Type'} (s : A -> Prop) : (term89 A B s) = (term89 A B s).
Proof. exact (fun_ext (fun p : A -> A => @lem5943309 A B p s)). Qed.
Lemma lem5943311 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5943312 {A B : Type'} (s : A -> Prop) : (term91 A B s) = (term91 A B s).
Proof. exact (MK_COMB (@lem5943311 A) (@lem5943310 A B s)). Qed.
Lemma lem5943313 {A B : Type'} : (term93 A B) = (term93 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5943312 A B s)). Qed.
Lemma lem5943314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5943315 {A B : Type'} : (term95 A B) = (term95 A B).
Proof. exact (MK_COMB (@lem5943314 A) (@lem5943313 A B)). Qed.
Lemma lem5943374 {A B : Type'} : (term94 A B) = (term95 A B).
Proof. exact (TRANS (@lem5943258 A B) (@lem5943315 A B)). Qed.
Lemma lem5943375 {A B : Type'} : (term95 A B) = (term94 A B).
Proof. exact (SYM (@lem5943374 A B)). Qed.
Lemma lem5943377 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term40 A p s.
Proof. exact (h1). Qed.
Lemma lem5943378 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) : term39 A s p.
Proof. exact (h1). Qed.
Lemma lem5943380 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5943381 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : ((@IN A x s) = (term45 A x p s)) = (term106 A x p s).
Proof. exact (@lem5943380 ((@IN A x s) = (term45 A x p s))). Qed.
Lemma lem5943382 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term106 A x p s) = ((@IN A x s) = (term45 A x p s)).
Proof. exact (SYM (@lem5943381 A x p s)). Qed.
Lemma lem5943383 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term107 A x p s) : term107 A x p s.
Proof. exact (h1). Qed.
Lemma lem5943396 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term104 A p x s) = (term108 A p x s).
Proof. exact (@lem17265 (@IN A x s) (term109 A p x s)). Qed.
Lemma lem5943397 {A : Type'} (p : A -> A) (s : A -> Prop) : (term105 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5943396 A p x s)). Qed.
Lemma lem5943398 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943451 {A : Type'} (p : A -> A) (s : A -> Prop) : (term40 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5943398 A) (@lem5943397 A p s)). Qed.
Lemma lem5943452 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5943451 A p s) (@lem5943377 A p s h1)). Qed.
Lemma lem5943462 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term112 A s p x y) = (term113 A s p x y).
Proof. exact (@lem17045 (@IN A x s) ((p x) = y)). Qed.
Lemma lem5943467 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5943468 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5943469 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term114 A s p y x') = (term98 A s p x' y).
Proof. exact (eq_refl (term114 A s p y x')). Qed.
Lemma lem5943470 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term112 A s p x' y) = (term113 A s p x' y).
Proof. exact (@lem5943462 A s p x' y). Qed.
Lemma lem5943471 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term115 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem5943472 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term116 A s p y).
Proof. exact (@lem5943471 A (term99 A s p y)). Qed.
Lemma lem5943473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5943474 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term117 A s p y x') = (term112 A s p x' y).
Proof. exact (MK_COMB (@lem5943473) (@lem5943469 A s p x' y)). Qed.
Lemma lem5943475 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term117 A s p y x') = (term113 A s p x' y).
Proof. exact (TRANS (@lem5943474 A s p x' y) (@lem5943470 A s p x' y)). Qed.
Lemma lem5943476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5943477 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term118 A s p y x') = (term119 A s p x' y).
Proof. exact (MK_COMB (@lem5943476) (@lem5943475 A s p x' y)). Qed.
Lemma lem5943478 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term120 A s p y x' x) = (term121 A s p y x' x).
Proof. exact (MK_COMB (@lem5943477 A s p x' y) (@lem5943467 A x' x)). Qed.
Lemma lem5943479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5943480 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term117 A s p y x) = (term112 A s p x y).
Proof. exact (MK_COMB (@lem5943479) (@lem5943468 A s p x y)). Qed.
Lemma lem5943481 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term117 A s p y x) = (term113 A s p x y).
Proof. exact (TRANS (@lem5943480 A s p x y) (@lem5943462 A s p x y)). Qed.
Lemma lem5943482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5943483 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term118 A s p y x) = (term119 A s p x y).
Proof. exact (MK_COMB (@lem5943482) (@lem5943481 A s p x y)). Qed.
Lemma lem5943484 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term122 A s p y x' x) = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5943483 A s p x y) (@lem5943478 A s p y x' x)). Qed.
Lemma lem5943485 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term124 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5943484 A s p y x' x)). Qed.
Lemma lem5943486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943487 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term126 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5943486 A) (@lem5943485 A s p y x)). Qed.
Lemma lem5943488 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term128 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943487 A s p y x)). Qed.
Lemma lem5943489 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943490 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term130 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5943489 A) (@lem5943488 A s p y)). Qed.
Lemma lem5943491 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5943492 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term132 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943491 A s p x y)). Qed.
Lemma lem5943493 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943494 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term133 A s p y) = (term134 A s p y).
Proof. exact (MK_COMB (@lem5943493 A) (@lem5943492 A s p y)). Qed.
Lemma lem5943495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5943496 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term135 A s p y) = (term136 A s p y).
Proof. exact (MK_COMB (@lem5943495) (@lem5943494 A s p y)). Qed.
Lemma lem5943497 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term116 A s p y) = (term137 A s p y).
Proof. exact (MK_COMB (@lem5943496 A s p y) (@lem5943490 A s p y)). Qed.
Lemma lem5943498 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term137 A s p y).
Proof. exact (TRANS (@lem5943472 A s p y) (@lem5943497 A s p y)). Qed.
Lemma lem5943500 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5943501 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term139 A s p y) = (term140 A s p y).
Proof. exact (MK_COMB (@lem5943500 A y s) (@lem5943498 A s p y)). Qed.
Lemma lem5943502 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term139 A s p y).
Proof. exact (@lem17265 (@IN A y s) (term100 A s p y)). Qed.
Lemma lem5943503 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term140 A s p y).
Proof. exact (TRANS (@lem5943502 A s p y) (@lem5943501 A s p y)). Qed.
Lemma lem5943504 {A : Type'} (s : A -> Prop) (p : A -> A) : (term103 A s p) = (term141 A s p).
Proof. exact (fun_ext (fun y : A => @lem5943503 A s p y)). Qed.
Lemma lem5943505 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943506 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term142 A s p).
Proof. exact (MK_COMB (@lem5943505 A) (@lem5943504 A s p)). Qed.
Lemma lem5943608 {A : Type'} (P : Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem5943609 {A : Type'} (P : Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (@lem5943608 A P Q). Qed.
Lemma lem5943610 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term146 A s p y x).
Proof. exact (@lem5943609 A (term113 A s p x y) (term147 A s p y x)). Qed.
Lemma lem5943611 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5943612 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5943613 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term149 A s p y x x') = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5943612 A s p x y) (@lem5943611 A s p y x' x)). Qed.
Lemma lem5943614 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term150 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5943613 A s p y x' x)). Qed.
Lemma lem5943615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943616 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5943615 A) (@lem5943614 A s p y x)). Qed.
Lemma lem5943617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5943618 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term151 A s p y x) = (term152 A s p y x).
Proof. exact (MK_COMB (@lem5943617) (@lem5943616 A s p y x)). Qed.
Lemma lem5943619 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5943620 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term153 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5943619 A s p y x' x)). Qed.
Lemma lem5943621 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943622 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term154 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5943621 A) (@lem5943620 A s p y x)). Qed.
Lemma lem5943623 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5943624 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5943623 A s p x y) (@lem5943622 A s p y x)). Qed.
Lemma lem5943625 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term145 A s p y x) = (term146 A s p y x)) = ((term127 A s p y x) = (term156 A s p y x)).
Proof. exact (MK_COMB (@lem5943618 A s p y x) (@lem5943624 A s p y x)). Qed.
Lemma lem5943626 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term127 A s p y x) = (term156 A s p y x).
Proof. exact (EQ_MP (@lem5943625 A s p y x) (@lem5943610 A s p y x)). Qed.
Lemma lem5943675 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term129 A s p y) = (term157 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943626 A s p y x)). Qed.
Lemma lem5943676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943677 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term131 A s p y) = (term158 A s p y).
Proof. exact (MK_COMB (@lem5943676 A) (@lem5943675 A s p y)). Qed.
Lemma lem5943726 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term136 A s p y) = (term136 A s p y).
Proof. exact (eq_refl (term136 A s p y)). Qed.
Lemma lem5943727 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term137 A s p y) = (term159 A s p y).
Proof. exact (MK_COMB (@lem5943726 A s p y) (@lem5943677 A s p y)). Qed.
Lemma lem5943728 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5943729 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term140 A s p y) = (term160 A s p y).
Proof. exact (MK_COMB (@lem5943728 A y s) (@lem5943727 A s p y)). Qed.
Lemma lem5943730 {A : Type'} (s : A -> Prop) (p : A -> A) : (term141 A s p) = (term161 A s p).
Proof. exact (fun_ext (fun y : A => @lem5943729 A s p y)). Qed.
Lemma lem5943731 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943732 {A : Type'} (s : A -> Prop) (p : A -> A) : (term142 A s p) = (term162 A s p).
Proof. exact (MK_COMB (@lem5943731 A) (@lem5943730 A s p)). Qed.
Lemma lem5943782 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5943783 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem5943782 A P Q). Qed.
Lemma lem5943784 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term165 A s p y) = (term166 A s p y).
Proof. exact (@lem5943783 A (term99 A s p y) (term158 A s p y)). Qed.
Lemma lem5943785 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5943786 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term132 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943785 A s p x y)). Qed.
Lemma lem5943787 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943788 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term133 A s p y) = (term134 A s p y).
Proof. exact (MK_COMB (@lem5943787 A) (@lem5943786 A s p y)). Qed.
Lemma lem5943789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5943790 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term135 A s p y) = (term136 A s p y).
Proof. exact (MK_COMB (@lem5943789) (@lem5943788 A s p y)). Qed.
Lemma lem5943791 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (eq_refl (term158 A s p y)). Qed.
Lemma lem5943792 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term165 A s p y) = (term159 A s p y).
Proof. exact (MK_COMB (@lem5943790 A s p y) (@lem5943791 A s p y)). Qed.
Lemma lem5943793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5943794 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term167 A s p y) = (term168 A s p y).
Proof. exact (MK_COMB (@lem5943793) (@lem5943792 A s p y)). Qed.
Lemma lem5943795 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5943796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5943797 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term169 A s p y x) = (term170 A s p x y).
Proof. exact (MK_COMB (@lem5943796) (@lem5943795 A s p x y)). Qed.
Lemma lem5943798 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (eq_refl (term158 A s p y)). Qed.
Lemma lem5943799 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term171 A x s p y) = (term172 A x s p y).
Proof. exact (MK_COMB (@lem5943797 A s p x y) (@lem5943798 A s p y)). Qed.
Lemma lem5943800 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term173 A s p y) = (term174 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943799 A x s p y)). Qed.
Lemma lem5943801 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943802 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term166 A s p y) = (term175 A s p y).
Proof. exact (MK_COMB (@lem5943801 A) (@lem5943800 A s p y)). Qed.
Lemma lem5943803 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term165 A s p y) = (term166 A s p y)) = ((term159 A s p y) = (term175 A s p y)).
Proof. exact (MK_COMB (@lem5943794 A s p y) (@lem5943802 A s p y)). Qed.
Lemma lem5943804 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term159 A s p y) = (term175 A s p y).
Proof. exact (EQ_MP (@lem5943803 A s p y) (@lem5943784 A s p y)). Qed.
Lemma lem5943805 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5943806 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term160 A s p y) = (term176 A s p y).
Proof. exact (MK_COMB (@lem5943805 A y s) (@lem5943804 A s p y)). Qed.
Lemma lem5943808 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5943809 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem5943808 A P Q). Qed.
Lemma lem5943810 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term179 A s p y) = (term180 A s p y).
Proof. exact (@lem5943809 A (term181 A y s) (term174 A s p y)). Qed.
Lemma lem5943811 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term182 A s p y x) = (term172 A x s p y).
Proof. exact (eq_refl (term182 A s p y x)). Qed.
Lemma lem5943812 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term183 A s p y) = (term174 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943811 A x s p y)). Qed.
Lemma lem5943813 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943814 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term184 A s p y) = (term175 A s p y).
Proof. exact (MK_COMB (@lem5943813 A) (@lem5943812 A s p y)). Qed.
Lemma lem5943815 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5943816 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term179 A s p y) = (term176 A s p y).
Proof. exact (MK_COMB (@lem5943815 A y s) (@lem5943814 A s p y)). Qed.
Lemma lem5943817 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5943818 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term185 A s p y) = (term186 A s p y).
Proof. exact (MK_COMB (@lem5943817) (@lem5943816 A s p y)). Qed.
Lemma lem5943819 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term182 A s p y x) = (term172 A x s p y).
Proof. exact (eq_refl (term182 A s p y x)). Qed.
Lemma lem5943820 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5943821 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term187 A s p y x) = (term188 A x s p y).
Proof. exact (MK_COMB (@lem5943820 A y s) (@lem5943819 A x s p y)). Qed.
Lemma lem5943822 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term189 A s p y) = (term190 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943821 A x s p y)). Qed.
Lemma lem5943823 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943824 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term180 A s p y) = (term191 A s p y).
Proof. exact (MK_COMB (@lem5943823 A) (@lem5943822 A s p y)). Qed.
Lemma lem5943825 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term179 A s p y) = (term180 A s p y)) = ((term176 A s p y) = (term191 A s p y)).
Proof. exact (MK_COMB (@lem5943818 A s p y) (@lem5943824 A s p y)). Qed.
Lemma lem5943826 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term176 A s p y) = (term191 A s p y).
Proof. exact (EQ_MP (@lem5943825 A s p y) (@lem5943810 A s p y)). Qed.
Lemma lem5943827 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term160 A s p y) = (term191 A s p y).
Proof. exact (TRANS (@lem5943806 A s p y) (@lem5943826 A s p y)). Qed.
Lemma lem5943828 {A : Type'} (s : A -> Prop) (p : A -> A) : (term161 A s p) = (term192 A s p).
Proof. exact (fun_ext (fun y : A => @lem5943827 A s p y)). Qed.
Lemma lem5943829 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943830 {A : Type'} (s : A -> Prop) (p : A -> A) : (term162 A s p) = (term193 A s p).
Proof. exact (MK_COMB (@lem5943829 A) (@lem5943828 A s p)). Qed.
Lemma lem5943832 {A B : Type'} (P : type1413 A B) : (term194 A B P) = (term195 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5943833 {A : Type'} (P : type1402 A) : (term196 A P) = (term197 A P).
Proof. exact (@lem5943832 A A P). Qed.
Lemma lem5943834 {A : Type'} (s : A -> Prop) (p : A -> A) : (term198 A s p) = (term199 A s p).
Proof. exact (@lem5943833 A (term200 A s p)). Qed.
Lemma lem5943835 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term201 A s p y) = (term190 A s p y).
Proof. exact (eq_refl (term201 A s p y)). Qed.
Lemma lem5943836 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5943837 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term202 A s p y x) = (term203 A s p y x).
Proof. exact (MK_COMB (@lem5943835 A s p y) (@lem5943836 A x)). Qed.
Lemma lem5943838 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term203 A s p y x) = (term188 A x s p y).
Proof. exact (eq_refl (term203 A s p y x)). Qed.
Lemma lem5943839 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term202 A s p y x) = (term188 A x s p y).
Proof. exact (TRANS (@lem5943837 A s p y x) (@lem5943838 A x s p y)). Qed.
Lemma lem5943840 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term204 A s p y) = (term190 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5943839 A x s p y)). Qed.
Lemma lem5943841 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943842 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term205 A s p y) = (term191 A s p y).
Proof. exact (MK_COMB (@lem5943841 A) (@lem5943840 A s p y)). Qed.
Lemma lem5943843 {A : Type'} (s : A -> Prop) (p : A -> A) : (term206 A s p) = (term192 A s p).
Proof. exact (fun_ext (fun y : A => @lem5943842 A s p y)). Qed.
Lemma lem5943844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943845 {A : Type'} (s : A -> Prop) (p : A -> A) : (term198 A s p) = (term193 A s p).
Proof. exact (MK_COMB (@lem5943844 A) (@lem5943843 A s p)). Qed.
Lemma lem5943846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5943847 {A : Type'} (s : A -> Prop) (p : A -> A) : (term207 A s p) = (term208 A s p).
Proof. exact (MK_COMB (@lem5943846) (@lem5943845 A s p)). Qed.
Lemma lem5943848 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term201 A s p y) = (term190 A s p y).
Proof. exact (eq_refl (term201 A s p y)). Qed.
Lemma lem5943849 {A : Type'} (x : A -> A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5943850 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) (y : A) : (term209 A s p x y) = (term210 A s p x y).
Proof. exact (MK_COMB (@lem5943848 A s p y) (@lem5943849 A x y)). Qed.
Lemma lem5943851 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term210 A s p x y) = (term211 A x s p y).
Proof. exact (eq_refl (term210 A s p x y)). Qed.
Lemma lem5943852 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term209 A s p x y) = (term211 A x s p y).
Proof. exact (TRANS (@lem5943850 A s p x y) (@lem5943851 A x s p y)). Qed.
Lemma lem5943853 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) : (term212 A s p x) = (term213 A x s p).
Proof. exact (fun_ext (fun y : A => @lem5943852 A x s p y)). Qed.
Lemma lem5943854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943855 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) : (term214 A s p x) = (term215 A x s p).
Proof. exact (MK_COMB (@lem5943854 A) (@lem5943853 A x s p)). Qed.
Lemma lem5943856 {A : Type'} (s : A -> Prop) (p : A -> A) : (term216 A s p) = (term217 A s p).
Proof. exact (fun_ext (fun x : A -> A => @lem5943855 A x s p)). Qed.
Lemma lem5943857 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5943858 {A : Type'} (s : A -> Prop) (p : A -> A) : (term199 A s p) = (term218 A s p).
Proof. exact (MK_COMB (@lem5943857 A) (@lem5943856 A s p)). Qed.
Lemma lem5943859 {A : Type'} (s : A -> Prop) (p : A -> A) : ((term198 A s p) = (term199 A s p)) = ((term193 A s p) = (term218 A s p)).
Proof. exact (MK_COMB (@lem5943847 A s p) (@lem5943858 A s p)). Qed.
Lemma lem5943860 {A : Type'} (s : A -> Prop) (p : A -> A) : (term193 A s p) = (term218 A s p).
Proof. exact (EQ_MP (@lem5943859 A s p) (@lem5943834 A s p)). Qed.
Lemma lem5943861 {A : Type'} (s : A -> Prop) (p : A -> A) : (term162 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5943830 A s p) (@lem5943860 A s p)). Qed.
Lemma lem5943862 {A : Type'} (s : A -> Prop) (p : A -> A) : (term142 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5943732 A s p) (@lem5943861 A s p)). Qed.
Lemma lem5943863 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5943506 A s p) (@lem5943862 A s p)). Qed.
Lemma lem5943864 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) : term218 A s p.
Proof. exact (EQ_MP (@lem5943863 A s p) (@lem5943378 A s p h1)). Qed.
Lemma lem5943875 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term219 A x p x' s) = (term220 A x p x' s).
Proof. exact (@lem17045 (x = (p x')) (@IN A x' s)). Qed.
Lemma lem5943878 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term96 A x p x' s) = (term96 A x p x' s).
Proof. exact (eq_refl (term96 A x p x' s)). Qed.
Lemma lem5943879 {A : Type'} (P : A -> Prop) : (term221 A P) = (term222 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem5943880 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term223 A x p s) = (term224 A x p s).
Proof. exact (@lem5943879 A (term97 A x p s)). Qed.
Lemma lem5943881 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term225 A x p s x') = (term96 A x p x' s).
Proof. exact (eq_refl (term225 A x p s x')). Qed.
Lemma lem5943882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5943883 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term226 A x p s x') = (term219 A x p x' s).
Proof. exact (MK_COMB (@lem5943882) (@lem5943881 A x p x' s)). Qed.
Lemma lem5943884 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term226 A x p s x') = (term220 A x p x' s).
Proof. exact (TRANS (@lem5943883 A x p x' s) (@lem5943875 A x p x' s)). Qed.
Lemma lem5943885 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term227 A x p s) = (term228 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5943884 A x p x' s)). Qed.
Lemma lem5943886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5943887 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term224 A x p s) = (term229 A x p s).
Proof. exact (MK_COMB (@lem5943886 A) (@lem5943885 A x p s)). Qed.
Lemma lem5943888 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term223 A x p s) = (term229 A x p s).
Proof. exact (TRANS (@lem5943880 A x p s) (@lem5943887 A x p s)). Qed.
Lemma lem5943889 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term97 A x p s) = (term97 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5943878 A x p x' s)). Qed.
Lemma lem5943890 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5943891 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term45 A x p s) = (term45 A x p s).
Proof. exact (MK_COMB (@lem5943890 A) (@lem5943889 A x p s)). Qed.
Lemma lem5943893 {A : Type'} (x : A) (s : A -> Prop) : (term230 A x s) = (term230 A x s).
Proof. exact (eq_refl (term230 A x s)). Qed.
Lemma lem5943894 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term231 A x p s) = (term231 A x p s).
Proof. exact (MK_COMB (@lem5943893 A x s) (@lem5943891 A x p s)). Qed.
Lemma lem5943896 {A : Type'} (x : A) (s : A -> Prop) : (term232 A x s) = (term232 A x s).
Proof. exact (eq_refl (term232 A x s)). Qed.
Lemma lem5943897 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term233 A x p s) = (term234 A x p s).
Proof. exact (MK_COMB (@lem5943896 A x s) (@lem5943888 A x p s)). Qed.
Lemma lem5943898 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5943899 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term235 A x p s) = (term236 A x p s).
Proof. exact (MK_COMB (@lem5943898) (@lem5943897 A x p s)). Qed.
Lemma lem5943900 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term237 A x p s) = (term238 A x p s).
Proof. exact (MK_COMB (@lem5943899 A x p s) (@lem5943894 A x p s)). Qed.
Lemma lem5943901 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term107 A x p s) = (term237 A x p s).
Proof. exact (@lem17646 (@IN A x s) (term45 A x p s)). Qed.
Lemma lem5943902 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term107 A x p s) = (term238 A x p s).
Proof. exact (TRANS (@lem5943901 A x p s) (@lem5943900 A x p s)). Qed.
Lemma lem5944001 {A : Type'} (P : Prop) (Q : A -> Prop) : (term239 A P Q) = (term240 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5944002 {A : Type'} (P : Prop) (Q : A -> Prop) : (term239 A P Q) = (term240 A P Q).
Proof. exact (@lem5944001 A P Q). Qed.
Lemma lem5944003 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term241 A x p s) = (term242 A x p s).
Proof. exact (@lem5944002 A (term181 A x s) (term97 A x p s)). Qed.
Lemma lem5944004 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term225 A x p s x') = (term96 A x p x' s).
Proof. exact (eq_refl (term225 A x p s x')). Qed.
Lemma lem5944005 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term243 A x p s) = (term97 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944004 A x p x' s)). Qed.
Lemma lem5944006 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5944007 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term244 A x p s) = (term45 A x p s).
Proof. exact (MK_COMB (@lem5944006 A) (@lem5944005 A x p s)). Qed.
Lemma lem5944008 {A : Type'} (x : A) (s : A -> Prop) : (term230 A x s) = (term230 A x s).
Proof. exact (eq_refl (term230 A x s)). Qed.
Lemma lem5944009 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term241 A x p s) = (term231 A x p s).
Proof. exact (MK_COMB (@lem5944008 A x s) (@lem5944007 A x p s)). Qed.
Lemma lem5944010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944011 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term245 A x p s) = (term246 A x p s).
Proof. exact (MK_COMB (@lem5944010) (@lem5944009 A x p s)). Qed.
Lemma lem5944012 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term225 A x p s x') = (term96 A x p x' s).
Proof. exact (eq_refl (term225 A x p s x')). Qed.
Lemma lem5944013 {A : Type'} (x : A) (s : A -> Prop) : (term230 A x s) = (term230 A x s).
Proof. exact (eq_refl (term230 A x s)). Qed.
Lemma lem5944014 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term247 A x p s x') = (term248 A x p x' s).
Proof. exact (MK_COMB (@lem5944013 A x s) (@lem5944012 A x p x' s)). Qed.
Lemma lem5944015 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term249 A x p s) = (term250 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944014 A x p x' s)). Qed.
Lemma lem5944016 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5944017 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term242 A x p s) = (term251 A x p s).
Proof. exact (MK_COMB (@lem5944016 A) (@lem5944015 A x p s)). Qed.
Lemma lem5944018 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : ((term241 A x p s) = (term242 A x p s)) = ((term231 A x p s) = (term251 A x p s)).
Proof. exact (MK_COMB (@lem5944011 A x p s) (@lem5944017 A x p s)). Qed.
Lemma lem5944019 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term231 A x p s) = (term251 A x p s).
Proof. exact (EQ_MP (@lem5944018 A x p s) (@lem5944003 A x p s)). Qed.
Lemma lem5944020 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term236 A x p s) = (term236 A x p s).
Proof. exact (eq_refl (term236 A x p s)). Qed.
Lemma lem5944021 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term238 A x p s) = (term252 A x p s).
Proof. exact (MK_COMB (@lem5944020 A x p s) (@lem5944019 A x p s)). Qed.
Lemma lem5944023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5944024 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem5944023 A P Q). Qed.
Lemma lem5944025 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term253 A x p s) = (term254 A x p s).
Proof. exact (@lem5944024 A (term234 A x p s) (term250 A x p s)). Qed.
Lemma lem5944026 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term255 A x p s x') = (term248 A x p x' s).
Proof. exact (eq_refl (term255 A x p s x')). Qed.
Lemma lem5944027 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term256 A x p s) = (term250 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944026 A x p x' s)). Qed.
Lemma lem5944028 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5944029 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term257 A x p s) = (term251 A x p s).
Proof. exact (MK_COMB (@lem5944028 A) (@lem5944027 A x p s)). Qed.
Lemma lem5944030 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term236 A x p s) = (term236 A x p s).
Proof. exact (eq_refl (term236 A x p s)). Qed.
Lemma lem5944031 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term253 A x p s) = (term252 A x p s).
Proof. exact (MK_COMB (@lem5944030 A x p s) (@lem5944029 A x p s)). Qed.
Lemma lem5944032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944033 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term258 A x p s) = (term259 A x p s).
Proof. exact (MK_COMB (@lem5944032) (@lem5944031 A x p s)). Qed.
Lemma lem5944034 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term255 A x p s x') = (term248 A x p x' s).
Proof. exact (eq_refl (term255 A x p s x')). Qed.
Lemma lem5944035 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term236 A x p s) = (term236 A x p s).
Proof. exact (eq_refl (term236 A x p s)). Qed.
Lemma lem5944036 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term260 A x p s x') = (term261 A x p x' s).
Proof. exact (MK_COMB (@lem5944035 A x p s) (@lem5944034 A x p x' s)). Qed.
Lemma lem5944037 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term262 A x p s) = (term263 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944036 A x p x' s)). Qed.
Lemma lem5944038 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5944039 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term254 A x p s) = (term264 A x p s).
Proof. exact (MK_COMB (@lem5944038 A) (@lem5944037 A x p s)). Qed.
Lemma lem5944040 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : ((term253 A x p s) = (term254 A x p s)) = ((term252 A x p s) = (term264 A x p s)).
Proof. exact (MK_COMB (@lem5944033 A x p s) (@lem5944039 A x p s)). Qed.
Lemma lem5944041 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term252 A x p s) = (term264 A x p s).
Proof. exact (EQ_MP (@lem5944040 A x p s) (@lem5944025 A x p s)). Qed.
Lemma lem5944043 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term238 A x p s) = (term264 A x p s).
Proof. exact (TRANS (@lem5944021 A x p s) (@lem5944041 A x p s)). Qed.
Lemma lem5944044 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term107 A x p s) = (term264 A x p s).
Proof. exact (TRANS (@lem5943902 A x p s) (@lem5944043 A x p s)). Qed.
Lemma lem5944045 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term107 A x p s) : term264 A x p s.
Proof. exact (EQ_MP (@lem5944044 A x p s) (@lem5943383 A x p s h1)). Qed.
Lemma lem5944046 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term261 A x p x' s) : term261 A x p x' s.
Proof. exact (h1). Qed.
Lemma lem5944047 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term215 A x'' s p.
Proof. exact (h1). Qed.
Lemma lem5944068 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term108 A p x s) = (term108 A p x s).
Proof. exact (eq_refl (term108 A p x s)). Qed.
Lemma lem5944069 {A : Type'} (p : A -> A) (s : A -> Prop) : (term110 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5944068 A p x s)). Qed.
Lemma lem5944070 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944071 {A : Type'} (p : A -> A) (s : A -> Prop) : (term111 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5944070 A) (@lem5944069 A p s)). Qed.
Lemma lem5944072 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5944071 A p s) (@lem5943452 A p s h1)). Qed.
Lemma lem5944097 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term248 A x p x' s) = (term248 A x p x' s).
Proof. exact (eq_refl (term248 A x p x' s)). Qed.
Lemma lem5944116 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term220 A x p x' s) = (term220 A x p x' s).
Proof. exact (eq_refl (term220 A x p x' s)). Qed.
Lemma lem5944117 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term228 A x p s) = (term228 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944116 A x p x' s)). Qed.
Lemma lem5944118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944119 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term229 A x p s) = (term229 A x p s).
Proof. exact (MK_COMB (@lem5944118 A) (@lem5944117 A x p s)). Qed.
Lemma lem5944126 {A : Type'} (x : A) (s : A -> Prop) : (term232 A x s) = (term232 A x s).
Proof. exact (eq_refl (term232 A x s)). Qed.
Lemma lem5944127 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term234 A x p s) = (term234 A x p s).
Proof. exact (MK_COMB (@lem5944126 A x s) (@lem5944119 A x p s)). Qed.
Lemma lem5944128 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5944129 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term236 A x p s) = (term236 A x p s).
Proof. exact (MK_COMB (@lem5944128) (@lem5944127 A x p s)). Qed.
Lemma lem5944130 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term261 A x p x' s) = (term261 A x p x' s).
Proof. exact (MK_COMB (@lem5944129 A x p s) (@lem5944097 A x p x' s)). Qed.
Lemma lem5944131 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term261 A x p x' s) : term261 A x p x' s.
Proof. exact (EQ_MP (@lem5944130 A x p x' s) (@lem5944046 A x p x' s h1)). Qed.
Lemma lem5944158 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term121 A s p y x' x) = (term121 A s p y x' x).
Proof. exact (eq_refl (term121 A s p y x' x)). Qed.
Lemma lem5944159 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term147 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944158 A s p y x' x)). Qed.
Lemma lem5944160 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944161 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term155 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5944160 A) (@lem5944159 A s p y x)). Qed.
Lemma lem5944182 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5944183 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term156 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5944182 A s p x y) (@lem5944161 A s p y x)). Qed.
Lemma lem5944184 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term157 A s p y) = (term157 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5944183 A s p y x)). Qed.
Lemma lem5944185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944186 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (MK_COMB (@lem5944185 A) (@lem5944184 A s p y)). Qed.
Lemma lem5944207 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944208 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x'' s p y) = (term266 A x'' s p y).
Proof. exact (MK_COMB (@lem5944207 A s p x'' y) (@lem5944186 A s p y)). Qed.
Lemma lem5944217 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944218 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x'' s p y) = (term211 A x'' s p y).
Proof. exact (MK_COMB (@lem5944217 A y s) (@lem5944208 A x'' s p y)). Qed.
Lemma lem5944219 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term213 A x'' s p) = (term213 A x'' s p).
Proof. exact (fun_ext (fun y : A => @lem5944218 A x'' s p y)). Qed.
Lemma lem5944220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944221 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x'' s p) = (term215 A x'' s p).
Proof. exact (MK_COMB (@lem5944220 A) (@lem5944219 A x'' s p)). Qed.
Lemma lem5944222 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term215 A x'' s p.
Proof. exact (EQ_MP (@lem5944221 A x'' s p) (@lem5944047 A x'' s p h1)). Qed.
Lemma lem5944223 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term234 A x p s.
Proof. exact (h1). Qed.
Lemma lem5944224 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term248 A x p x' s.
Proof. exact (h1). Qed.
Lemma lem5944225 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term229 A x p s.
Proof. exact (proj2 (@lem5944223 A x p s h1)). Qed.
Lemma lem5944227 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term96 A x p x' s.
Proof. exact (proj2 (@lem5944224 A x p x' s h1)). Qed.
Lemma lem5944249 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5944250 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5944249 A P Q). Qed.
Lemma lem5944251 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term145 A s p y x).
Proof. exact (@lem5944250 A (term113 A s p x y) (term147 A s p y x)). Qed.
Lemma lem5944252 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5944253 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term153 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944252 A s p y x' x)). Qed.
Lemma lem5944254 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944255 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term154 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5944254 A) (@lem5944253 A s p y x)). Qed.
Lemma lem5944256 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5944257 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5944256 A s p x y) (@lem5944255 A s p y x)). Qed.
Lemma lem5944258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944259 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term267 A s p y x) = (term268 A s p y x).
Proof. exact (MK_COMB (@lem5944258) (@lem5944257 A s p y x)). Qed.
Lemma lem5944260 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5944261 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5944262 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term149 A s p y x x') = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5944261 A s p x y) (@lem5944260 A s p y x' x)). Qed.
Lemma lem5944263 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term150 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944262 A s p y x' x)). Qed.
Lemma lem5944264 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944265 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5944264 A) (@lem5944263 A s p y x)). Qed.
Lemma lem5944266 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term146 A s p y x) = (term145 A s p y x)) = ((term156 A s p y x) = (term127 A s p y x)).
Proof. exact (MK_COMB (@lem5944259 A s p y x) (@lem5944265 A s p y x)). Qed.
Lemma lem5944267 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term156 A s p y x) = (term127 A s p y x).
Proof. exact (EQ_MP (@lem5944266 A s p y x) (@lem5944251 A s p y x)). Qed.
Lemma lem5944268 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term157 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5944267 A s p y x)). Qed.
Lemma lem5944269 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944270 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5944269 A) (@lem5944268 A s p y)). Qed.
Lemma lem5944271 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944272 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x'' s p y) = (term269 A x'' s p y).
Proof. exact (MK_COMB (@lem5944271 A s p x'' y) (@lem5944270 A s p y)). Qed.
Lemma lem5944274 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5944275 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem5944274 A P Q). Qed.
Lemma lem5944276 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term272 A x'' s p y) = (term273 A x'' s p y).
Proof. exact (@lem5944275 A (term274 A s p x'' y) (term129 A s p y)). Qed.
Lemma lem5944277 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term275 A s p y x) = (term127 A s p y x).
Proof. exact (eq_refl (term275 A s p y x)). Qed.
Lemma lem5944278 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term276 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5944277 A s p y x)). Qed.
Lemma lem5944279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944280 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term277 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5944279 A) (@lem5944278 A s p y)). Qed.
Lemma lem5944281 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944282 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term272 A x'' s p y) = (term269 A x'' s p y).
Proof. exact (MK_COMB (@lem5944281 A s p x'' y) (@lem5944280 A s p y)). Qed.
Lemma lem5944283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944284 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term278 A x'' s p y) = (term279 A x'' s p y).
Proof. exact (MK_COMB (@lem5944283) (@lem5944282 A x'' s p y)). Qed.
Lemma lem5944285 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term275 A s p y x) = (term127 A s p y x).
Proof. exact (eq_refl (term275 A s p y x)). Qed.
Lemma lem5944286 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944287 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term280 A x'' s p y x) = (term281 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944286 A s p x'' y) (@lem5944285 A s p y x)). Qed.
Lemma lem5944288 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term282 A x'' s p y) = (term283 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944287 A x'' s p y x)). Qed.
Lemma lem5944289 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944290 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term273 A x'' s p y) = (term284 A x'' s p y).
Proof. exact (MK_COMB (@lem5944289 A) (@lem5944288 A x'' s p y)). Qed.
Lemma lem5944291 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : ((term272 A x'' s p y) = (term273 A x'' s p y)) = ((term269 A x'' s p y) = (term284 A x'' s p y)).
Proof. exact (MK_COMB (@lem5944284 A x'' s p y) (@lem5944290 A x'' s p y)). Qed.
Lemma lem5944292 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term269 A x'' s p y) = (term284 A x'' s p y).
Proof. exact (EQ_MP (@lem5944291 A x'' s p y) (@lem5944276 A x'' s p y)). Qed.
Lemma lem5944294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5944295 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem5944294 A P Q). Qed.
Lemma lem5944296 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term285 A x'' s p y x) = (term286 A x'' s p y x).
Proof. exact (@lem5944295 A (term274 A s p x'' y) (term125 A s p y x)). Qed.
Lemma lem5944297 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term287 A s p y x x') = (term123 A s p y x' x).
Proof. exact (eq_refl (term287 A s p y x x')). Qed.
Lemma lem5944298 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term288 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944297 A s p y x' x)). Qed.
Lemma lem5944299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944300 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term289 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5944299 A) (@lem5944298 A s p y x)). Qed.
Lemma lem5944301 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944302 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term285 A x'' s p y x) = (term281 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944301 A s p x'' y) (@lem5944300 A s p y x)). Qed.
Lemma lem5944303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944304 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term290 A x'' s p y x) = (term291 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944303) (@lem5944302 A x'' s p y x)). Qed.
Lemma lem5944305 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term287 A s p y x x') = (term123 A s p y x' x).
Proof. exact (eq_refl (term287 A s p y x x')). Qed.
Lemma lem5944306 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term265 A s p x'' y) = (term265 A s p x'' y).
Proof. exact (eq_refl (term265 A s p x'' y)). Qed.
Lemma lem5944307 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term292 A x'' s p y x x') = (term293 A x'' s p y x' x).
Proof. exact (MK_COMB (@lem5944306 A s p x'' y) (@lem5944305 A s p y x' x)). Qed.
Lemma lem5944308 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term294 A x'' s p y x) = (term295 A x'' s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944307 A x'' s p y x' x)). Qed.
Lemma lem5944309 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944310 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term286 A x'' s p y x) = (term296 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944309 A) (@lem5944308 A x'' s p y x)). Qed.
Lemma lem5944311 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term285 A x'' s p y x) = (term286 A x'' s p y x)) = ((term281 A x'' s p y x) = (term296 A x'' s p y x)).
Proof. exact (MK_COMB (@lem5944304 A x'' s p y x) (@lem5944310 A x'' s p y x)). Qed.
Lemma lem5944312 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term281 A x'' s p y x) = (term296 A x'' s p y x).
Proof. exact (EQ_MP (@lem5944311 A x'' s p y x) (@lem5944296 A x'' s p y x)). Qed.
Lemma lem5944313 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term283 A x'' s p y) = (term297 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944312 A x'' s p y x)). Qed.
Lemma lem5944314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944315 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term284 A x'' s p y) = (term298 A x'' s p y).
Proof. exact (MK_COMB (@lem5944314 A) (@lem5944313 A x'' s p y)). Qed.
Lemma lem5944316 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term269 A x'' s p y) = (term298 A x'' s p y).
Proof. exact (TRANS (@lem5944292 A x'' s p y) (@lem5944315 A x'' s p y)). Qed.
Lemma lem5944317 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x'' s p y) = (term298 A x'' s p y).
Proof. exact (TRANS (@lem5944272 A x'' s p y) (@lem5944316 A x'' s p y)). Qed.
Lemma lem5944318 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944319 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x'' s p y) = (term299 A x'' s p y).
Proof. exact (MK_COMB (@lem5944318 A y s) (@lem5944317 A x'' s p y)). Qed.
Lemma lem5944321 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5944322 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5944321 A P Q). Qed.
Lemma lem5944323 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term300 A x'' s p y) = (term301 A x'' s p y).
Proof. exact (@lem5944322 A (term181 A y s) (term297 A x'' s p y)). Qed.
Lemma lem5944324 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term302 A x'' s p y x) = (term296 A x'' s p y x).
Proof. exact (eq_refl (term302 A x'' s p y x)). Qed.
Lemma lem5944325 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term303 A x'' s p y) = (term297 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944324 A x'' s p y x)). Qed.
Lemma lem5944326 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944327 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term304 A x'' s p y) = (term298 A x'' s p y).
Proof. exact (MK_COMB (@lem5944326 A) (@lem5944325 A x'' s p y)). Qed.
Lemma lem5944328 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944329 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term300 A x'' s p y) = (term299 A x'' s p y).
Proof. exact (MK_COMB (@lem5944328 A y s) (@lem5944327 A x'' s p y)). Qed.
Lemma lem5944330 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944331 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term305 A x'' s p y) = (term306 A x'' s p y).
Proof. exact (MK_COMB (@lem5944330) (@lem5944329 A x'' s p y)). Qed.
Lemma lem5944332 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term302 A x'' s p y x) = (term296 A x'' s p y x).
Proof. exact (eq_refl (term302 A x'' s p y x)). Qed.
Lemma lem5944333 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944334 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term307 A x'' s p y x) = (term308 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944333 A y s) (@lem5944332 A x'' s p y x)). Qed.
Lemma lem5944335 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term309 A x'' s p y) = (term310 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944334 A x'' s p y x)). Qed.
Lemma lem5944336 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944337 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term301 A x'' s p y) = (term311 A x'' s p y).
Proof. exact (MK_COMB (@lem5944336 A) (@lem5944335 A x'' s p y)). Qed.
Lemma lem5944338 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : ((term300 A x'' s p y) = (term301 A x'' s p y)) = ((term299 A x'' s p y) = (term311 A x'' s p y)).
Proof. exact (MK_COMB (@lem5944331 A x'' s p y) (@lem5944337 A x'' s p y)). Qed.
Lemma lem5944339 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term299 A x'' s p y) = (term311 A x'' s p y).
Proof. exact (EQ_MP (@lem5944338 A x'' s p y) (@lem5944323 A x'' s p y)). Qed.
Lemma lem5944341 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5944342 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5944341 A P Q). Qed.
Lemma lem5944343 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A x'' s p y x) = (term313 A x'' s p y x).
Proof. exact (@lem5944342 A (term181 A y s) (term295 A x'' s p y x)). Qed.
Lemma lem5944344 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term314 A x'' s p y x x') = (term293 A x'' s p y x' x).
Proof. exact (eq_refl (term314 A x'' s p y x x')). Qed.
Lemma lem5944345 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term315 A x'' s p y x) = (term295 A x'' s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944344 A x'' s p y x' x)). Qed.
Lemma lem5944346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944347 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term316 A x'' s p y x) = (term296 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944346 A) (@lem5944345 A x'' s p y x)). Qed.
Lemma lem5944348 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944349 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A x'' s p y x) = (term308 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944348 A y s) (@lem5944347 A x'' s p y x)). Qed.
Lemma lem5944350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944351 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term317 A x'' s p y x) = (term318 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944350) (@lem5944349 A x'' s p y x)). Qed.
Lemma lem5944352 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term314 A x'' s p y x x') = (term293 A x'' s p y x' x).
Proof. exact (eq_refl (term314 A x'' s p y x x')). Qed.
Lemma lem5944353 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5944354 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term319 A x'' s p y x x') = (term320 A x'' s p y x' x).
Proof. exact (MK_COMB (@lem5944353 A y s) (@lem5944352 A x'' s p y x' x)). Qed.
Lemma lem5944355 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term321 A x'' s p y x) = (term322 A x'' s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944354 A x'' s p y x' x)). Qed.
Lemma lem5944356 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944357 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term313 A x'' s p y x) = (term323 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944356 A) (@lem5944355 A x'' s p y x)). Qed.
Lemma lem5944358 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term312 A x'' s p y x) = (term313 A x'' s p y x)) = ((term308 A x'' s p y x) = (term323 A x'' s p y x)).
Proof. exact (MK_COMB (@lem5944351 A x'' s p y x) (@lem5944357 A x'' s p y x)). Qed.
Lemma lem5944359 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term308 A x'' s p y x) = (term323 A x'' s p y x).
Proof. exact (EQ_MP (@lem5944358 A x'' s p y x) (@lem5944343 A x'' s p y x)). Qed.
Lemma lem5944360 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term310 A x'' s p y) = (term324 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944359 A x'' s p y x)). Qed.
Lemma lem5944361 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944362 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term311 A x'' s p y) = (term325 A x'' s p y).
Proof. exact (MK_COMB (@lem5944361 A) (@lem5944360 A x'' s p y)). Qed.
Lemma lem5944363 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term299 A x'' s p y) = (term325 A x'' s p y).
Proof. exact (TRANS (@lem5944339 A x'' s p y) (@lem5944362 A x'' s p y)). Qed.
Lemma lem5944364 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x'' s p y) = (term325 A x'' s p y).
Proof. exact (TRANS (@lem5944319 A x'' s p y) (@lem5944363 A x'' s p y)). Qed.
Lemma lem5944365 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term213 A x'' s p) = (term326 A x'' s p).
Proof. exact (fun_ext (fun y : A => @lem5944364 A x'' s p y)). Qed.
Lemma lem5944366 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944367 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x'' s p) = (term327 A x'' s p).
Proof. exact (MK_COMB (@lem5944366 A) (@lem5944365 A x'' s p)). Qed.
Lemma lem5944405 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term320 A x'' s p y x' x) = (term328 A x'' s p y x' x).
Proof. exact (@lem19490 (term274 A s p x'' y) (term181 A y s) (term123 A s p y x' x)). Qed.
Lemma lem5944406 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term329 A s p y x' x) = (term329 A s p y x' x).
Proof. exact (eq_refl (term329 A s p y x' x)). Qed.
Lemma lem5944413 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term330 A s p x'' y) = (term331 A s p x'' y).
Proof. exact (@lem19490 (term109 A x'' y s) (term181 A y s) ((term332 A p x'' y) = y)). Qed.
Lemma lem5944414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5944415 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (y : A) : (term333 A s p x'' y) = (term334 A s p x'' y).
Proof. exact (MK_COMB (@lem5944414) (@lem5944413 A s p x'' y)). Qed.
Lemma lem5944416 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term328 A x'' s p y x' x) = (term335 A x'' s p y x' x).
Proof. exact (MK_COMB (@lem5944415 A s p x'' y) (@lem5944406 A s p y x' x)). Qed.
Lemma lem5944418 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term320 A x'' s p y x' x) = (term335 A x'' s p y x' x).
Proof. exact (TRANS (@lem5944405 A x'' s p y x' x) (@lem5944416 A x'' s p y x' x)). Qed.
Lemma lem5944419 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term322 A x'' s p y x) = (term336 A x'' s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5944418 A x'' s p y x' x)). Qed.
Lemma lem5944420 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944421 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term323 A x'' s p y x) = (term337 A x'' s p y x).
Proof. exact (MK_COMB (@lem5944420 A) (@lem5944419 A x'' s p y x)). Qed.
Lemma lem5944422 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term324 A x'' s p y) = (term338 A x'' s p y).
Proof. exact (fun_ext (fun x : A => @lem5944421 A x'' s p y x)). Qed.
Lemma lem5944423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944424 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term325 A x'' s p y) = (term339 A x'' s p y).
Proof. exact (MK_COMB (@lem5944423 A) (@lem5944422 A x'' s p y)). Qed.
Lemma lem5944425 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term326 A x'' s p) = (term340 A x'' s p).
Proof. exact (fun_ext (fun y : A => @lem5944424 A x'' s p y)). Qed.
Lemma lem5944426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944427 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term327 A x'' s p) = (term341 A x'' s p).
Proof. exact (MK_COMB (@lem5944426 A) (@lem5944425 A x'' s p)). Qed.
Lemma lem5944428 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x'' s p) = (term341 A x'' s p).
Proof. exact (TRANS (@lem5944367 A x'' s p) (@lem5944427 A x'' s p)). Qed.
Lemma lem5944429 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term341 A x'' s p.
Proof. exact (EQ_MP (@lem5944428 A x'' s p) (@lem5944222 A x'' s p h1)). Qed.
Lemma lem5944441 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : (term220 A x p x' s) = (term220 A x p x' s).
Proof. exact (eq_refl (term220 A x p x' s)). Qed.
Lemma lem5944442 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term228 A x p s) = (term228 A x p s).
Proof. exact (fun_ext (fun x' : A => @lem5944441 A x p x' s)). Qed.
Lemma lem5944443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944445 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) : (term229 A x p s) = (term229 A x p s).
Proof. exact (MK_COMB (@lem5944443 A) (@lem5944442 A x p s)). Qed.
Lemma lem5944446 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term229 A x p s.
Proof. exact (EQ_MP (@lem5944445 A x p s) (@lem5944225 A x p s h1)). Qed.
Lemma lem5944458 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term108 A p x s) = (term108 A p x s).
Proof. exact (eq_refl (term108 A p x s)). Qed.
Lemma lem5944459 {A : Type'} (p : A -> A) (s : A -> Prop) : (term110 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5944458 A p x s)). Qed.
Lemma lem5944460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5944462 {A : Type'} (p : A -> A) (s : A -> Prop) : (term111 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5944460 A) (@lem5944459 A p s)). Qed.
Lemma lem5944463 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5944462 A p s) (@lem5944072 A p s h1)). Qed.
Lemma lem5944661 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term342 A x'' s p _75134.
Proof. exact (@lem5944429 A x'' s p h1 _75134). Qed.
Lemma lem5944662 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (_75134 : A) : (term342 A x'' s p _75134) = (term339 A x'' s p _75134).
Proof. exact (eq_refl (term342 A x'' s p _75134)). Qed.
Lemma lem5944663 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term339 A x'' s p _75134.
Proof. exact (EQ_MP (@lem5944662 A x'' s p _75134) (@lem5944661 A _75134 x'' s p h1)). Qed.
Lemma lem5944664 {A : Type'} (_75134 : A) (_75135 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term343 A x'' s p _75134 _75135.
Proof. exact (@lem5944663 A _75134 x'' s p h1 _75135). Qed.
Lemma lem5944665 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (_75134 : A) (_75135 : A) : (term343 A x'' s p _75134 _75135) = (term337 A x'' s p _75134 _75135).
Proof. exact (eq_refl (term343 A x'' s p _75134 _75135)). Qed.
Lemma lem5944666 {A : Type'} (_75134 : A) (_75135 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term337 A x'' s p _75134 _75135.
Proof. exact (EQ_MP (@lem5944665 A x'' s p _75134 _75135) (@lem5944664 A _75134 _75135 x'' s p h1)). Qed.
Lemma lem5944667 {A : Type'} (_75134 : A) (_75135 : A) (_75136 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term344 A x'' s p _75134 _75135 _75136.
Proof. exact (@lem5944666 A _75134 _75135 x'' s p h1 _75136). Qed.
Lemma lem5944668 {A : Type'} (x'' : A -> A) (s : A -> Prop) (p : A -> A) (_75134 : A) (_75136 : A) (_75135 : A) : (term344 A x'' s p _75134 _75135 _75136) = (term335 A x'' s p _75134 _75136 _75135).
Proof. exact (eq_refl (term344 A x'' s p _75134 _75135 _75136)). Qed.
Lemma lem5944669 {A : Type'} (_75134 : A) (_75136 : A) (_75135 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term335 A x'' s p _75134 _75136 _75135.
Proof. exact (EQ_MP (@lem5944668 A x'' s p _75134 _75136 _75135) (@lem5944667 A _75134 _75135 _75136 x'' s p h1)). Qed.
Lemma lem5944670 {A : Type'} (_75137 : A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term345 A x p s _75137.
Proof. exact (@lem5944446 A x p s h1 _75137). Qed.
Lemma lem5944671 {A : Type'} (x : A) (p : A -> A) (_75137 : A) (s : A -> Prop) : (term345 A x p s _75137) = (term220 A x p _75137 s).
Proof. exact (eq_refl (term345 A x p s _75137)). Qed.
Lemma lem5944673 {A : Type'} (_75138 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term346 A p s _75138.
Proof. exact (@lem5944463 A p s h1 _75138). Qed.
Lemma lem5944674 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term346 A p s _75138) = (term108 A p _75138 s).
Proof. exact (eq_refl (term346 A p s _75138)). Qed.
Lemma lem5944686 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term331 A s p x'' _75134.
Proof. exact (proj1 (@lem5944669 A _75134 (@el A) (@el A) x'' s p h1)). Qed.
Lemma lem5944708 {A : Type'} (_75137 : A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term220 A x p _75137 s.
Proof. exact (EQ_MP (@lem5944671 A x p _75137 s) (@lem5944670 A _75137 x p s h1)). Qed.
Lemma lem5944740 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term108 A x'' _75134 s.
Proof. exact (proj1 (@lem5944686 A _75134 x'' s p h1)). Qed.
Lemma lem5944746 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term347 A s p x'' _75134.
Proof. exact (proj2 (@lem5944686 A _75134 x'' s p h1)). Qed.
Lemma lem5944756 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term181 A x s.
Proof. exact (proj1 (@lem5944224 A x p x' s h1)). Qed.
Lemma lem5944758 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : x = (p x').
Proof. exact (proj1 (@lem5944227 A x p x' s h1)). Qed.
Lemma lem5944840 {A : Type'} (_75138 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term108 A p _75138 s.
Proof. exact (EQ_MP (@lem5944674 A p _75138 s) (@lem5944673 A _75138 p s h1)). Qed.
Lemma lem5944841 {A : Type'} (s : A -> Prop) : (term348 A s) = (term348 A s).
Proof. exact (eq_refl (term348 A s)). Qed.
Lemma lem5944842 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : (term349 A s x) = (term350 A s p x').
Proof. exact (MK_COMB (@lem5944841 A s) (@lem5944758 A x p x' s h1)). Qed.
Lemma lem5944843 {A : Type'} (p : A -> A) (x' : A) (s : A -> Prop) : (term350 A s p x') = (term351 A p x' s).
Proof. exact (eq_refl (term350 A s p x')). Qed.
Lemma lem5944844 {A : Type'} (s : A -> Prop) (x : A) : (term352 A s x) = (term352 A s x).
Proof. exact (eq_refl (term352 A s x)). Qed.
Lemma lem5944845 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : ((term349 A s x) = (term350 A s p x')) = ((term349 A s x) = (term351 A p x' s)).
Proof. exact (MK_COMB (@lem5944844 A s x) (@lem5944843 A p x' s)). Qed.
Lemma lem5944846 {A : Type'} (x : A) (s : A -> Prop) : (term349 A s x) = (term181 A x s).
Proof. exact (eq_refl (term349 A s x)). Qed.
Lemma lem5944847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944848 {A : Type'} (x : A) (s : A -> Prop) : (term352 A s x) = (term353 A x s).
Proof. exact (MK_COMB (@lem5944847) (@lem5944846 A x s)). Qed.
Lemma lem5944849 {A : Type'} (p : A -> A) (x' : A) (s : A -> Prop) : (term351 A p x' s) = (term351 A p x' s).
Proof. exact (eq_refl (term351 A p x' s)). Qed.
Lemma lem5944850 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : ((term349 A s x) = (term351 A p x' s)) = ((term181 A x s) = (term351 A p x' s)).
Proof. exact (MK_COMB (@lem5944848 A x s) (@lem5944849 A p x' s)). Qed.
Lemma lem5944851 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) : ((term349 A s x) = (term350 A s p x')) = ((term181 A x s) = (term351 A p x' s)).
Proof. exact (TRANS (@lem5944845 A x p x' s) (@lem5944850 A x p x' s)). Qed.
Lemma lem5944852 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : (term181 A x s) = (term351 A p x' s).
Proof. exact (EQ_MP (@lem5944851 A x p x' s) (@lem5944842 A x p x' s h1)). Qed.
Lemma lem5944853 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term351 A p x' s.
Proof. exact (EQ_MP (@lem5944852 A x p x' s h1) (@lem5944756 A x p x' s h1)). Qed.
Lemma lem5944958 {A : Type'} (x : A) (y : A) (z : A) : term354 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem5944964 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : @IN A x s.
Proof. exact (proj1 (@lem5944223 A x p s h1)). Qed.
Lemma lem5944965 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term355 A x s.
Proof. exact (fun h0 : term181 A x s => @lem5944964 A x p s h1). Qed.
Lemma lem5944967 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5944968 {A : Type'} (x : A) (s : A -> Prop) : (term355 A x s) = (@IN A x s).
Proof. exact (@lem5944967 (@IN A x s)). Qed.
Lemma lem5944969 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : @IN A x s.
Proof. exact (EQ_MP (@lem5944968 A x s) (@lem5944965 A x p s h1)). Qed.
Lemma lem5944975 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5944976 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term347 A s p x'' _75134) = (term357 A p x'' _75134 s).
Proof. exact (@lem5944975 ((term332 A p x'' _75134) = _75134) (term181 A _75134 s)). Qed.
Lemma lem5944984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5944985 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term358 A s p x'' _75134) = (term359 A p x'' _75134 s).
Proof. exact (MK_COMB (@lem5944984) (@lem5944976 A p x'' _75134 s)). Qed.
Lemma lem5944993 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term357 A p x'' _75134 s) = (term357 A p x'' _75134 s).
Proof. exact (eq_refl (term357 A p x'' _75134 s)). Qed.
Lemma lem5944994 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term347 A s p x'' _75134) = (term357 A p x'' _75134 s)) = ((term357 A p x'' _75134 s) = (term357 A p x'' _75134 s)).
Proof. exact (MK_COMB (@lem5944985 A p x'' _75134 s) (@lem5944993 A p x'' _75134 s)). Qed.
Lemma lem5944996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5944997 (x : Prop) : (x = x) = True.
Proof. exact (@lem5944996 Prop x). Qed.
Lemma lem5944998 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term357 A p x'' _75134 s) = (term357 A p x'' _75134 s)) = True.
Proof. exact (@lem5944997 (term357 A p x'' _75134 s)). Qed.
Lemma lem5944999 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term347 A s p x'' _75134) = (term357 A p x'' _75134 s)) = True.
Proof. exact (TRANS (@lem5944994 A p x'' _75134 s) (@lem5944998 A p x'' _75134 s)). Qed.
Lemma lem5945000 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : True = ((term347 A s p x'' _75134) = (term357 A p x'' _75134 s)).
Proof. exact (SYM (@lem5944999 A p x'' _75134 s)). Qed.
Lemma lem5945001 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term347 A s p x'' _75134) = (term357 A p x'' _75134 s).
Proof. exact (EQ_MP (@lem5945000 A p x'' _75134 s) (@lem0)). Qed.
Lemma lem5945002 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term357 A p x'' _75134 s.
Proof. exact (EQ_MP (@lem5945001 A p x'' _75134 s) (@lem5944746 A _75134 x'' s p h1)). Qed.
Lemma lem5945004 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5945005 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (_75134 : A) : (term357 A p x'' _75134 s) = (term361 A s p x'' _75134).
Proof. exact (@lem5945004 (term181 A _75134 s) ((term332 A p x'' _75134) = _75134)). Qed.
Lemma lem5945007 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5945008 {A : Type'} (_75134 : A) (s : A -> Prop) : (term362 A _75134 s) = (@IN A _75134 s).
Proof. exact (@lem5945007 (@IN A _75134 s)). Qed.
Lemma lem5945009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945010 {A : Type'} (_75134 : A) (s : A -> Prop) : (term363 A _75134 s) = (term101 A _75134 s).
Proof. exact (MK_COMB (@lem5945009) (@lem5945008 A _75134 s)). Qed.
Lemma lem5945011 {A : Type'} (p : A -> A) (x'' : A -> A) (_75134 : A) : ((term332 A p x'' _75134) = _75134) = ((term332 A p x'' _75134) = _75134).
Proof. exact (eq_refl ((term332 A p x'' _75134) = _75134)). Qed.
Lemma lem5945012 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (_75134 : A) : (term361 A s p x'' _75134) = (term364 A s p x'' _75134).
Proof. exact (MK_COMB (@lem5945010 A _75134 s) (@lem5945011 A p x'' _75134)). Qed.
Lemma lem5945013 {A : Type'} (s : A -> Prop) (p : A -> A) (x'' : A -> A) (_75134 : A) : (term357 A p x'' _75134 s) = (term364 A s p x'' _75134).
Proof. exact (TRANS (@lem5945005 A s p x'' _75134) (@lem5945012 A s p x'' _75134)). Qed.
Lemma lem5945016 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term364 A s p x'' _75134.
Proof. exact (EQ_MP (@lem5945013 A s p x'' _75134) (@lem5945002 A _75134 x'' s p h1)). Qed.
Lemma lem5945017 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term364 A s p x'' _75134.
Proof. exact (@lem5945016 A _75134 x'' s p h1). Qed.
Lemma lem5945018 {A : Type'} (x : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term364 A s p x'' x.
Proof. exact (@lem5945017 A x x'' s p h1). Qed.
Lemma lem5945021 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : (term332 A p x'' x) = x.
Proof. exact (@lem5945018 A x x'' s p h1 (@lem5944969 A x p s h2)). Qed.
Lemma lem5945022 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term365 A p x'' x.
Proof. exact (fun h0 : term366 A p x'' x => @lem5945021 A x'' x p s h1 h2). Qed.
Lemma lem5945024 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945025 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : (term365 A p x'' x) = ((term332 A p x'' x) = x).
Proof. exact (@lem5945024 ((term332 A p x'' x) = x)). Qed.
Lemma lem5945026 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : (term332 A p x'' x) = x.
Proof. exact (EQ_MP (@lem5945025 A p x'' x) (@lem5945022 A x'' x p s h1 h2)). Qed.
Lemma lem5945028 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5945029 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5945028 A x). Qed.
Lemma lem5945030 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : (term332 A p x'' x) = (term332 A p x'' x).
Proof. exact (@lem5945029 A (term332 A p x'' x)). Qed.
Lemma lem5945031 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : term367 A p x'' x.
Proof. exact (fun h0 : term368 A p x'' x => @lem5945030 A p x'' x). Qed.
Lemma lem5945033 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945034 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : (term367 A p x'' x) = ((term332 A p x'' x) = (term332 A p x'' x)).
Proof. exact (@lem5945033 ((term332 A p x'' x) = (term332 A p x'' x))). Qed.
Lemma lem5945035 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : (term332 A p x'' x) = (term332 A p x'' x).
Proof. exact (EQ_MP (@lem5945034 A p x'' x) (@lem5945031 A p x'' x)). Qed.
Lemma lem5945053 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5945054 {A : Type'} (y : A) (x : A) (z : A) : (term369 A x y z) = (term370 A y x z).
Proof. exact (@lem5945053 (y = z) (term371 A x z)). Qed.
Lemma lem5945064 {A : Type'} (x : A) (y : A) : (term372 A x y) = (term372 A x y).
Proof. exact (eq_refl (term372 A x y)). Qed.
Lemma lem5945065 {A : Type'} (y : A) (x : A) (z : A) : (term354 A x y z) = (term373 A y x z).
Proof. exact (MK_COMB (@lem5945064 A x y) (@lem5945054 A y x z)). Qed.
Lemma lem5945069 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5945070 {A : Type'} (y : A) (x : A) (z : A) : (term373 A y x z) = (term374 A y x z).
Proof. exact (@lem5945069 (y = z) (term371 A x y) (term371 A x z)). Qed.
Lemma lem5945092 {A : Type'} (y : A) (x : A) (z : A) : (term354 A x y z) = (term374 A y x z).
Proof. exact (TRANS (@lem5945065 A y x z) (@lem5945070 A y x z)). Qed.
Lemma lem5945093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5945094 {A : Type'} (y : A) (x : A) (z : A) : (term375 A x y z) = (term376 A y x z).
Proof. exact (MK_COMB (@lem5945093) (@lem5945092 A y x z)). Qed.
Lemma lem5945116 {A : Type'} (y : A) (x : A) (z : A) : (term374 A y x z) = (term374 A y x z).
Proof. exact (eq_refl (term374 A y x z)). Qed.
Lemma lem5945117 {A : Type'} (y : A) (x : A) (z : A) : ((term354 A x y z) = (term374 A y x z)) = ((term374 A y x z) = (term374 A y x z)).
Proof. exact (MK_COMB (@lem5945094 A y x z) (@lem5945116 A y x z)). Qed.
Lemma lem5945119 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5945120 (x : Prop) : (x = x) = True.
Proof. exact (@lem5945119 Prop x). Qed.
Lemma lem5945121 {A : Type'} (y : A) (x : A) (z : A) : ((term374 A y x z) = (term374 A y x z)) = True.
Proof. exact (@lem5945120 (term374 A y x z)). Qed.
Lemma lem5945122 {A : Type'} (y : A) (x : A) (z : A) : ((term354 A x y z) = (term374 A y x z)) = True.
Proof. exact (TRANS (@lem5945117 A y x z) (@lem5945121 A y x z)). Qed.
Lemma lem5945123 {A : Type'} (y : A) (x : A) (z : A) : True = ((term354 A x y z) = (term374 A y x z)).
Proof. exact (SYM (@lem5945122 A y x z)). Qed.
Lemma lem5945124 {A : Type'} (y : A) (x : A) (z : A) : (term354 A x y z) = (term374 A y x z).
Proof. exact (EQ_MP (@lem5945123 A y x z) (@lem0)). Qed.
Lemma lem5945125 {A : Type'} (y : A) (x : A) (z : A) : term374 A y x z.
Proof. exact (EQ_MP (@lem5945124 A y x z) (@lem5944958 A x y z)). Qed.
Lemma lem5945127 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5945128 {A : Type'} (x : A) (y : A) (z : A) : (term374 A y x z) = (term377 A x y z).
Proof. exact (@lem5945127 (term378 A y x z) (y = z)). Qed.
Lemma lem5945130 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5945131 {A : Type'} (y : A) (x : A) (z : A) : (term381 A y x z) = (term382 A y x z).
Proof. exact (@lem5945130 (term371 A x y) (term371 A x z)). Qed.
Lemma lem5945133 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5945134 {A : Type'} (x : A) (y : A) : (term383 A x y) = (x = y).
Proof. exact (@lem5945133 (x = y)). Qed.
Lemma lem5945135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5945136 {A : Type'} (x : A) (y : A) : (term384 A x y) = (term385 A x y).
Proof. exact (MK_COMB (@lem5945135) (@lem5945134 A x y)). Qed.
Lemma lem5945138 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5945139 {A : Type'} (x : A) (z : A) : (term383 A x z) = (x = z).
Proof. exact (@lem5945138 (x = z)). Qed.
Lemma lem5945140 {A : Type'} (y : A) (x : A) (z : A) : (term382 A y x z) = (term386 A y x z).
Proof. exact (MK_COMB (@lem5945136 A x y) (@lem5945139 A x z)). Qed.
Lemma lem5945141 {A : Type'} (y : A) (x : A) (z : A) : (term381 A y x z) = (term386 A y x z).
Proof. exact (TRANS (@lem5945131 A y x z) (@lem5945140 A y x z)). Qed.
Lemma lem5945142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945143 {A : Type'} (y : A) (x : A) (z : A) : (term387 A y x z) = (term388 A y x z).
Proof. exact (MK_COMB (@lem5945142) (@lem5945141 A y x z)). Qed.
Lemma lem5945144 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5945145 {A : Type'} (x : A) (y : A) (z : A) : (term377 A x y z) = (term389 A x y z).
Proof. exact (MK_COMB (@lem5945143 A y x z) (@lem5945144 A y z)). Qed.
Lemma lem5945146 {A : Type'} (x : A) (y : A) (z : A) : (term374 A y x z) = (term389 A x y z).
Proof. exact (TRANS (@lem5945128 A x y z) (@lem5945145 A x y z)). Qed.
Lemma lem5945148 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term390 A p x'' x.
Proof. exact (conj (@lem5945026 A x'' x p s h1 h2) (@lem5945035 A p x'' x)). Qed.
Lemma lem5945150 {A : Type'} (x : A) (y : A) (z : A) : term389 A x y z.
Proof. exact (EQ_MP (@lem5945146 A x y z) (@lem5945125 A y x z)). Qed.
Lemma lem5945151 {A : Type'} (x : A) (y : A) (z : A) : term389 A x y z.
Proof. exact (@lem5945150 A x y z). Qed.
Lemma lem5945152 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : term391 A p x'' x.
Proof. exact (@lem5945151 A (term332 A p x'' x) x (term332 A p x'' x)). Qed.
Lemma lem5945155 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : x = (term332 A p x'' x).
Proof. exact (@lem5945152 A p x'' x (@lem5945148 A x'' x p s h1 h2)). Qed.
Lemma lem5945156 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term392 A p x'' x.
Proof. exact (fun h0 : term393 A p x'' x => @lem5945155 A x'' x p s h1 h2). Qed.
Lemma lem5945158 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945159 {A : Type'} (p : A -> A) (x'' : A -> A) (x : A) : (term392 A p x'' x) = (x = (term332 A p x'' x)).
Proof. exact (@lem5945158 (x = (term332 A p x'' x))). Qed.
Lemma lem5945160 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : x = (term332 A p x'' x).
Proof. exact (EQ_MP (@lem5945159 A p x'' x) (@lem5945156 A x'' x p s h1 h2)). Qed.
Lemma lem5945162 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : @IN A x s.
Proof. exact (proj1 (@lem5944223 A x p s h1)). Qed.
Lemma lem5945163 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term355 A x s.
Proof. exact (fun h0 : term181 A x s => @lem5945162 A x p s h1). Qed.
Lemma lem5945165 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945166 {A : Type'} (x : A) (s : A -> Prop) : (term355 A x s) = (@IN A x s).
Proof. exact (@lem5945165 (@IN A x s)). Qed.
Lemma lem5945167 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : @IN A x s.
Proof. exact (EQ_MP (@lem5945166 A x s) (@lem5945163 A x p s h1)). Qed.
Lemma lem5945173 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5945174 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term108 A x'' _75134 s) = (term394 A x'' _75134 s).
Proof. exact (@lem5945173 (term109 A x'' _75134 s) (term181 A _75134 s)). Qed.
Lemma lem5945180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5945181 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term395 A x'' _75134 s) = (term396 A x'' _75134 s).
Proof. exact (MK_COMB (@lem5945180) (@lem5945174 A x'' _75134 s)). Qed.
Lemma lem5945187 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term394 A x'' _75134 s) = (term394 A x'' _75134 s).
Proof. exact (eq_refl (term394 A x'' _75134 s)). Qed.
Lemma lem5945188 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term108 A x'' _75134 s) = (term394 A x'' _75134 s)) = ((term394 A x'' _75134 s) = (term394 A x'' _75134 s)).
Proof. exact (MK_COMB (@lem5945181 A x'' _75134 s) (@lem5945187 A x'' _75134 s)). Qed.
Lemma lem5945190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5945191 (x : Prop) : (x = x) = True.
Proof. exact (@lem5945190 Prop x). Qed.
Lemma lem5945192 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term394 A x'' _75134 s) = (term394 A x'' _75134 s)) = True.
Proof. exact (@lem5945191 (term394 A x'' _75134 s)). Qed.
Lemma lem5945193 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : ((term108 A x'' _75134 s) = (term394 A x'' _75134 s)) = True.
Proof. exact (TRANS (@lem5945188 A x'' _75134 s) (@lem5945192 A x'' _75134 s)). Qed.
Lemma lem5945194 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : True = ((term108 A x'' _75134 s) = (term394 A x'' _75134 s)).
Proof. exact (SYM (@lem5945193 A x'' _75134 s)). Qed.
Lemma lem5945195 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term108 A x'' _75134 s) = (term394 A x'' _75134 s).
Proof. exact (EQ_MP (@lem5945194 A x'' _75134 s) (@lem0)). Qed.
Lemma lem5945196 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term394 A x'' _75134 s.
Proof. exact (EQ_MP (@lem5945195 A x'' _75134 s) (@lem5944740 A _75134 x'' s p h1)). Qed.
Lemma lem5945198 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5945199 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term394 A x'' _75134 s) = (term397 A x'' _75134 s).
Proof. exact (@lem5945198 (term181 A _75134 s) (term109 A x'' _75134 s)). Qed.
Lemma lem5945201 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5945202 {A : Type'} (_75134 : A) (s : A -> Prop) : (term362 A _75134 s) = (@IN A _75134 s).
Proof. exact (@lem5945201 (@IN A _75134 s)). Qed.
Lemma lem5945203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945204 {A : Type'} (_75134 : A) (s : A -> Prop) : (term363 A _75134 s) = (term101 A _75134 s).
Proof. exact (MK_COMB (@lem5945203) (@lem5945202 A _75134 s)). Qed.
Lemma lem5945205 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term109 A x'' _75134 s) = (term109 A x'' _75134 s).
Proof. exact (eq_refl (term109 A x'' _75134 s)). Qed.
Lemma lem5945206 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term397 A x'' _75134 s) = (term104 A x'' _75134 s).
Proof. exact (MK_COMB (@lem5945204 A _75134 s) (@lem5945205 A x'' _75134 s)). Qed.
Lemma lem5945207 {A : Type'} (x'' : A -> A) (_75134 : A) (s : A -> Prop) : (term394 A x'' _75134 s) = (term104 A x'' _75134 s).
Proof. exact (TRANS (@lem5945199 A x'' _75134 s) (@lem5945206 A x'' _75134 s)). Qed.
Lemma lem5945210 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term104 A x'' _75134 s.
Proof. exact (EQ_MP (@lem5945207 A x'' _75134 s) (@lem5945196 A _75134 x'' s p h1)). Qed.
Lemma lem5945211 {A : Type'} (_75134 : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term104 A x'' _75134 s.
Proof. exact (@lem5945210 A _75134 x'' s p h1). Qed.
Lemma lem5945212 {A : Type'} (x : A) (x'' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x'' s p) : term104 A x'' x s.
Proof. exact (@lem5945211 A x x'' s p h1). Qed.
Lemma lem5945215 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term109 A x'' x s.
Proof. exact (@lem5945212 A x x'' s p h1 (@lem5945167 A x p s h2)). Qed.
Lemma lem5945216 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term398 A x'' x s.
Proof. exact (fun h0 : term351 A x'' x s => @lem5945215 A x'' x p s h1 h2). Qed.
Lemma lem5945218 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945219 {A : Type'} (x'' : A -> A) (x : A) (s : A -> Prop) : (term398 A x'' x s) = (term109 A x'' x s).
Proof. exact (@lem5945218 (term109 A x'' x s)). Qed.
Lemma lem5945220 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term109 A x'' x s.
Proof. exact (EQ_MP (@lem5945219 A x'' x s) (@lem5945216 A x'' x p s h1 h2)). Qed.
Lemma lem5945222 (a : Prop) (b : Prop) : (term399 a b) = (term400 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5945223 {A : Type'} (x : A) (p : A -> A) (_75137 : A) (s : A -> Prop) : (term220 A x p _75137 s) = (term219 A x p _75137 s).
Proof. exact (@lem5945222 (x = (p _75137)) (@IN A _75137 s)). Qed.
Lemma lem5945225 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5945226 {A : Type'} (x : A) (p : A -> A) (_75137 : A) (s : A -> Prop) : (term219 A x p _75137 s) = (term401 A x p _75137 s).
Proof. exact (@lem5945225 (term96 A x p _75137 s)). Qed.
Lemma lem5945227 {A : Type'} (x : A) (p : A -> A) (_75137 : A) (s : A -> Prop) : (term220 A x p _75137 s) = (term401 A x p _75137 s).
Proof. exact (TRANS (@lem5945223 A x p _75137 s) (@lem5945226 A x p _75137 s)). Qed.
Lemma lem5945229 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term402 A p x'' x s.
Proof. exact (conj (@lem5945160 A x'' x p s h1 h2) (@lem5945220 A x'' x p s h1 h2)). Qed.
Lemma lem5945231 {A : Type'} (_75137 : A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term401 A x p _75137 s.
Proof. exact (EQ_MP (@lem5945227 A x p _75137 s) (@lem5944708 A _75137 x p s h1)). Qed.
Lemma lem5945232 {A : Type'} (_75137 : A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term401 A x p _75137 s.
Proof. exact (@lem5945231 A _75137 x p s h1). Qed.
Lemma lem5945233 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term234 A x p s) : term403 A p x'' x s.
Proof. exact (@lem5945232 A (x'' x) x p s h1). Qed.
Lemma lem5945236 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : False.
Proof. exact (@lem5945233 A x'' x p s h2 (@lem5945229 A x'' x p s h1 h2)). Qed.
Lemma lem5945237 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : term404.
Proof. exact (fun h0 : ~ False => @lem5945236 A x'' x p s h1 h2). Qed.
Lemma lem5945239 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945240 : term404 = False.
Proof. exact (@lem5945239 False). Qed.
Lemma lem5945241 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (s : A -> Prop) (h1 : term215 A x'' s p) (h2 : term234 A x p s) : False.
Proof. exact (EQ_MP (@lem5945240) (@lem5945237 A x'' x p s h1 h2)). Qed.
Lemma lem5945296 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : @IN A x' s.
Proof. exact (proj2 (@lem5944227 A x p x' s h1)). Qed.
Lemma lem5945297 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term355 A x' s.
Proof. exact (fun h0 : term181 A x' s => @lem5945296 A x p x' s h1). Qed.
Lemma lem5945299 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945300 {A : Type'} (x' : A) (s : A -> Prop) : (term355 A x' s) = (@IN A x' s).
Proof. exact (@lem5945299 (@IN A x' s)). Qed.
Lemma lem5945301 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem5945300 A x' s) (@lem5945297 A x p x' s h1)). Qed.
Lemma lem5945307 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5945308 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term108 A p _75138 s) = (term394 A p _75138 s).
Proof. exact (@lem5945307 (term109 A p _75138 s) (term181 A _75138 s)). Qed.
Lemma lem5945314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5945315 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term395 A p _75138 s) = (term396 A p _75138 s).
Proof. exact (MK_COMB (@lem5945314) (@lem5945308 A p _75138 s)). Qed.
Lemma lem5945321 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term394 A p _75138 s) = (term394 A p _75138 s).
Proof. exact (eq_refl (term394 A p _75138 s)). Qed.
Lemma lem5945322 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : ((term108 A p _75138 s) = (term394 A p _75138 s)) = ((term394 A p _75138 s) = (term394 A p _75138 s)).
Proof. exact (MK_COMB (@lem5945315 A p _75138 s) (@lem5945321 A p _75138 s)). Qed.
Lemma lem5945324 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5945325 (x : Prop) : (x = x) = True.
Proof. exact (@lem5945324 Prop x). Qed.
Lemma lem5945326 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : ((term394 A p _75138 s) = (term394 A p _75138 s)) = True.
Proof. exact (@lem5945325 (term394 A p _75138 s)). Qed.
Lemma lem5945327 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : ((term108 A p _75138 s) = (term394 A p _75138 s)) = True.
Proof. exact (TRANS (@lem5945322 A p _75138 s) (@lem5945326 A p _75138 s)). Qed.
Lemma lem5945328 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : True = ((term108 A p _75138 s) = (term394 A p _75138 s)).
Proof. exact (SYM (@lem5945327 A p _75138 s)). Qed.
Lemma lem5945329 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term108 A p _75138 s) = (term394 A p _75138 s).
Proof. exact (EQ_MP (@lem5945328 A p _75138 s) (@lem0)). Qed.
Lemma lem5945330 {A : Type'} (_75138 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term394 A p _75138 s.
Proof. exact (EQ_MP (@lem5945329 A p _75138 s) (@lem5944840 A _75138 p s h1)). Qed.
Lemma lem5945332 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5945333 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term394 A p _75138 s) = (term397 A p _75138 s).
Proof. exact (@lem5945332 (term181 A _75138 s) (term109 A p _75138 s)). Qed.
Lemma lem5945335 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5945336 {A : Type'} (_75138 : A) (s : A -> Prop) : (term362 A _75138 s) = (@IN A _75138 s).
Proof. exact (@lem5945335 (@IN A _75138 s)). Qed.
Lemma lem5945337 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945338 {A : Type'} (_75138 : A) (s : A -> Prop) : (term363 A _75138 s) = (term101 A _75138 s).
Proof. exact (MK_COMB (@lem5945337) (@lem5945336 A _75138 s)). Qed.
Lemma lem5945339 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term109 A p _75138 s) = (term109 A p _75138 s).
Proof. exact (eq_refl (term109 A p _75138 s)). Qed.
Lemma lem5945340 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term397 A p _75138 s) = (term104 A p _75138 s).
Proof. exact (MK_COMB (@lem5945338 A _75138 s) (@lem5945339 A p _75138 s)). Qed.
Lemma lem5945341 {A : Type'} (p : A -> A) (_75138 : A) (s : A -> Prop) : (term394 A p _75138 s) = (term104 A p _75138 s).
Proof. exact (TRANS (@lem5945333 A p _75138 s) (@lem5945340 A p _75138 s)). Qed.
Lemma lem5945344 {A : Type'} (_75138 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p _75138 s.
Proof. exact (EQ_MP (@lem5945341 A p _75138 s) (@lem5945330 A _75138 p s h1)). Qed.
Lemma lem5945345 {A : Type'} (_75138 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p _75138 s.
Proof. exact (@lem5945344 A _75138 p s h1). Qed.
Lemma lem5945346 {A : Type'} (x' : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p x' s.
Proof. exact (@lem5945345 A x' p s h1). Qed.
Lemma lem5945349 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : term109 A p x' s.
Proof. exact (@lem5945346 A x' p s h1 (@lem5945301 A x p x' s h2)). Qed.
Lemma lem5945350 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : term398 A p x' s.
Proof. exact (fun h0 : term351 A p x' s => @lem5945349 A x p x' s h1 h2). Qed.
Lemma lem5945352 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945353 {A : Type'} (p : A -> A) (x' : A) (s : A -> Prop) : (term398 A p x' s) = (term109 A p x' s).
Proof. exact (@lem5945352 (term109 A p x' s)). Qed.
Lemma lem5945354 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : term109 A p x' s.
Proof. exact (EQ_MP (@lem5945353 A p x' s) (@lem5945350 A x p x' s h1 h2)). Qed.
Lemma lem5945357 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5945359 {A : Type'} (p : A -> A) (x' : A) (s : A -> Prop) : (term351 A p x' s) = (term405 A p x' s).
Proof. exact (@lem5945357 (term109 A p x' s)). Qed.
Lemma lem5945362 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term248 A x p x' s) : term405 A p x' s.
Proof. exact (EQ_MP (@lem5945359 A p x' s) (@lem5944853 A x p x' s h1)). Qed.
Lemma lem5945365 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : False.
Proof. exact (@lem5945362 A x p x' s h2 (@lem5945354 A x p x' s h1 h2)). Qed.
Lemma lem5945366 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : term404.
Proof. exact (fun h0 : ~ False => @lem5945365 A x p x' s h1 h2). Qed.
Lemma lem5945368 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5945369 : term404 = False.
Proof. exact (@lem5945368 False). Qed.
Lemma lem5945371 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term248 A x p x' s) : False.
Proof. exact (EQ_MP (@lem5945369) (@lem5945366 A x p x' s h1 h2)). Qed.
Lemma lem5945372 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term215 A x'' s p) (h3 : term261 A x p x' s) : False.
Proof. exact (or_elim (@lem5944131 A x p x' s h3) (fun h0 : term234 A x p s => @lem5945241 A x'' x p s h2 h0) (fun h0 : term248 A x p x' s => @lem5945371 A x p x' s h1 h0)). Qed.
Lemma lem5945373 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term215 A x'' s p) (h3 : term261 A x p x' s) : (term215 A x'' s p) = False.
Proof. exact (prop_ext (fun h4 : term215 A x'' s p => @lem5945372 A x'' x p x' s h1 h2 h3) (fun h4 : False => @lem5944222 A x'' s p h2)). Qed.
Lemma lem5945374 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term215 A x'' s p) (h3 : term261 A x p x' s) : False.
Proof. exact (EQ_MP (@lem5945373 A x'' x p x' s h1 h2 h3) (@lem5944222 A x'' s p h2)). Qed.
Lemma lem5945375 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term215 A x'' s p) (h3 : term261 A x p x' s) : (term261 A x p x' s) = False.
Proof. exact (prop_ext (fun h4 : term261 A x p x' s => @lem5945374 A x'' x p x' s h1 h2 h3) (fun h4 : False => @lem5944131 A x p x' s h3)). Qed.
Lemma lem5945376 {A : Type'} (x'' : A -> A) (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term40 A p s) (h2 : term215 A x'' s p) (h3 : term261 A x p x' s) : False.
Proof. exact (EQ_MP (@lem5945375 A x'' x p x' s h1 h2 h3) (@lem5944131 A x p x' s h3)). Qed.
Lemma lem5945377 {A : Type'} (x : A) (p : A -> A) (x' : A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term261 A x p x' s) : False.
Proof. exact (ex_elim (@lem5943864 A s p h1) (fun x'' : A -> A => fun h0 : term217 A s p x'' => @lem5945376 A x'' x p x' s h2 h0 h3)). Qed.
Lemma lem5945378 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term107 A x p s) : False.
Proof. exact (ex_elim (@lem5944045 A x p s h3) (fun x' : A => fun h0 : term263 A x p s x' => @lem5945377 A x p x' s h1 h2 h0)). Qed.
Lemma lem5945379 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term107 A x p s) : (term107 A x p s) = False.
Proof. exact (prop_ext (fun h4 : term107 A x p s => @lem5945378 A x p s h1 h2 h3) (fun h4 : False => @lem5943383 A x p s h3)). Qed.
Lemma lem5945380 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term107 A x p s) : False.
Proof. exact (EQ_MP (@lem5945379 A x p s h1 h2 h3) (@lem5943383 A x p s h3)). Qed.
Lemma lem5945381 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term106 A x p s.
Proof. exact (fun h0 : term107 A x p s => @lem5945380 A x p s h1 h2 h0). Qed.
Lemma lem5945382 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : (@IN A x s) = (term45 A x p s).
Proof. exact (EQ_MP (@lem5943382 A x p s) (@lem5945381 A x p s h1 h2)). Qed.
Lemma lem5945387 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term49 A p s.
Proof. exact (fun x : A => @lem5945382 A x p s h1 h2). Qed.
Lemma lem5945388 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term78 A p s.
Proof. exact (fun h0 : term39 A s p => @lem5945387 A p s h0 h1). Qed.
Lemma lem5945389 {A : Type'} (p : A -> A) (s : A -> Prop) : term81 A p s.
Proof. exact (fun h0 : term40 A p s => @lem5945388 A p s h0). Qed.
Lemma lem5945390 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term83 A B op p s.
Proof. exact (fun h0 : @monoidal B op => @lem5945389 A p s). Qed.
Lemma lem5945395 {A B : Type'} (p : A -> A) (s : A -> Prop) : term87 A B p s.
Proof. exact (fun op : type1400 B => @lem5945390 A B op p s). Qed.
Lemma lem5945400 {A B : Type'} (s : A -> Prop) : term91 A B s.
Proof. exact (fun p : A -> A => @lem5945395 A B p s). Qed.
Lemma lem5945405 {A B : Type'} : term95 A B.
Proof. exact (fun s : A -> Prop => @lem5945400 A B s). Qed.
Lemma lem5945406 {A B : Type'} : term94 A B.
Proof. exact (EQ_MP (@lem5943375 A B) (@lem5945405 A B)). Qed.
Lemma lem5945407 {A B : Type'} (s : A -> Prop) : term406 A B s.
Proof. exact (@lem5945406 A B s). Qed.
Lemma lem5945408 {A B : Type'} (s : A -> Prop) : (term406 A B s) = (term90 A B s).
Proof. exact (eq_refl (term406 A B s)). Qed.
Lemma lem5945409 {A B : Type'} (s : A -> Prop) : term90 A B s.
Proof. exact (EQ_MP (@lem5945408 A B s) (@lem5945407 A B s)). Qed.
Lemma lem5945410 {A B : Type'} (s : A -> Prop) (p : A -> A) : term407 A B s p.
Proof. exact (@lem5945409 A B s p). Qed.
Lemma lem5945411 {A B : Type'} (p : A -> A) (s : A -> Prop) : (term407 A B s p) = (term86 A B p s).
Proof. exact (eq_refl (term407 A B s p)). Qed.
Lemma lem5945412 {A B : Type'} (p : A -> A) (s : A -> Prop) : term86 A B p s.
Proof. exact (EQ_MP (@lem5945411 A B p s) (@lem5945410 A B s p)). Qed.
Lemma lem5945413 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) : term408 A B p s op.
Proof. exact (@lem5945412 A B p s op). Qed.
Lemma lem5945414 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : (term408 A B p s op) = (term70 A B op p s).
Proof. exact (eq_refl (term408 A B p s op)). Qed.
Lemma lem5945415 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term70 A B op p s.
Proof. exact (EQ_MP (@lem5945414 A B op p s) (@lem5945413 A B p s op)). Qed.
Lemma lem5945417 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) : term70 A B op p s.
Proof. exact (@lem5943128 A B op p s (@lem5945415 A B op p s)). Qed.
Lemma lem5945418 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term80 A p s.
Proof. exact (@lem5945417 A B op p s (@lem5943013 B op h1)). Qed.
Lemma lem5945419 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term40 A p s) (h2 : @monoidal B op) : term77 A p s.
Proof. exact (@lem5945418 A B p s op h2 (@lem5943016 A p s h1)). Qed.
Lemma lem5945420 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : term68 A p s.
Proof. exact (@lem5945419 A B p s op h2 h3 (@lem5943015 A s p h1)). Qed.
Lemma lem5945421 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) (h4 : term69 A p s) : False.
Proof. exact (@lem5945420 A B p s op h1 h2 h3 (@lem5943112 A p s h4)). Qed.
Lemma lem5945422 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) (h4 : term69 A p s) : (term69 A p s) = False.
Proof. exact (prop_ext (fun h5 : term69 A p s => @lem5945421 A B op p s h1 h2 h3 h4) (fun h5 : False => @lem5943112 A p s h4)). Qed.
Lemma lem5945423 {A B : Type'} (op : type1400 B) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) (h4 : term69 A p s) : False.
Proof. exact (EQ_MP (@lem5945422 A B op p s h1 h2 h3 h4) (@lem5943112 A p s h4)). Qed.
Lemma lem5945424 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : term68 A p s.
Proof. exact (fun h0 : term69 A p s => @lem5945423 A B op p s h1 h2 h3 h0). Qed.
Lemma lem5945425 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : term49 A p s.
Proof. exact (EQ_MP (@lem5943111 A p s) (@lem5945424 A B p s op h1 h2 h3)). Qed.
Lemma lem5945427 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5945428 {A : Type'} (s : A -> Prop) (p : A -> A) : (term57 A s p) = (term409 A s p).
Proof. exact (@lem5945427 (term57 A s p)). Qed.
Lemma lem5945429 {A : Type'} (s : A -> Prop) (p : A -> A) : (term409 A s p) = (term57 A s p).
Proof. exact (SYM (@lem5945428 A s p)). Qed.
Lemma lem5945430 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term410 A s p) : term410 A s p.
Proof. exact (h1). Qed.
Lemma lem5945433 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term411 A s p) : term411 A s p.
Proof. exact (h1). Qed.
Lemma lem5945434 {A : Type'} (s : A -> Prop) (p : A -> A) : term412 A s p.
Proof. exact (fun h0 : term411 A s p => @lem5945433 A s p h0). Qed.
Lemma lem5945435 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term412 A s p) : term412 A s p.
Proof. exact (h1). Qed.
Lemma lem5945436 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term411 A s p) : term411 A s p.
Proof. exact (h1). Qed.
Lemma lem5945437 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term411 A s p) (h2 : term412 A s p) : term411 A s p.
Proof. exact (@lem5945435 A s p h2 (@lem5945436 A s p h1)). Qed.
Lemma lem5945438 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term411 A s p) : term413 A s p.
Proof. exact (fun h0 : term412 A s p => @lem5945437 A s p h1 h0). Qed.
Lemma lem5945439 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term412 A s p) : term412 A s p.
Proof. exact (h1). Qed.
Lemma lem5945440 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term411 A s p) (h2 : term412 A s p) : term411 A s p.
Proof. exact (@lem5945438 A s p h1 (@lem5945439 A s p h2)). Qed.
Lemma lem5945441 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term412 A s p) : term412 A s p.
Proof. exact (fun h0 : term411 A s p => @lem5945440 A s p h0 h1). Qed.
Lemma lem5945442 {A : Type'} (s : A -> Prop) (p : A -> A) : term414 A s p.
Proof. exact (fun h0 : term412 A s p => @lem5945441 A s p h0). Qed.
Lemma lem5945445 {A : Type'} (s : A -> Prop) (p : A -> A) : term412 A s p.
Proof. exact (@lem5945442 A s p (@lem5945434 A s p)). Qed.
Lemma lem5945446 {A : Type'} (s : A -> Prop) (p : A -> A) : term412 A s p.
Proof. exact (@lem5945445 A s p). Qed.
Lemma lem5945474 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5945475 {A : Type'} (s : A -> Prop) (p : A -> A) : (term409 A s p) = (term415 A s p).
Proof. exact (@lem5945474 (term410 A s p)). Qed.
Lemma lem5945477 (t : Prop) : (term75 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5945478 {A : Type'} (s : A -> Prop) (p : A -> A) : (term415 A s p) = (term57 A s p).
Proof. exact (@lem5945477 (term57 A s p)). Qed.
Lemma lem5945483 {A : Type'} (s : A -> Prop) (p : A -> A) : (term409 A s p) = (term57 A s p).
Proof. exact (TRANS (@lem5945475 A s p) (@lem5945478 A s p)). Qed.
Lemma lem5945494 {A : Type'} (s : A -> Prop) (p : A -> A) : (term76 A s p) = (term76 A s p).
Proof. exact (eq_refl (term76 A s p)). Qed.
Lemma lem5945495 {A : Type'} (s : A -> Prop) (p : A -> A) : (term416 A s p) = (term417 A s p).
Proof. exact (MK_COMB (@lem5945494 A s p) (@lem5945483 A s p)). Qed.
Lemma lem5945498 {A : Type'} (p : A -> A) (s : A -> Prop) : (term79 A p s) = (term79 A p s).
Proof. exact (eq_refl (term79 A p s)). Qed.
Lemma lem5945499 {A : Type'} (s : A -> Prop) (p : A -> A) : (term411 A s p) = (term418 A s p).
Proof. exact (MK_COMB (@lem5945498 A p s) (@lem5945495 A s p)). Qed.
Lemma lem5945502 {A : Type'} (p : A -> A) : (term419 A p) = (term420 A p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5945499 A s p)). Qed.
Lemma lem5945503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5945504 {A : Type'} (p : A -> A) : (term421 A p) = (term422 A p).
Proof. exact (MK_COMB (@lem5945503 A) (@lem5945502 A p)). Qed.
Lemma lem5945509 {A : Type'} : (term423 A) = (term424 A).
Proof. exact (fun_ext (fun p : A -> A => @lem5945504 A p)). Qed.
Lemma lem5945510 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5945519 {A : Type'} : (term425 A) = (term426 A).
Proof. exact (MK_COMB (@lem5945510 A) (@lem5945509 A)). Qed.
Lemma lem5945532 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term427 A s p x y) = (term427 A s p x y).
Proof. exact (eq_refl (term427 A s p x y)). Qed.
Lemma lem5945533 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term428 A s p x) = (term428 A s p x).
Proof. exact (fun_ext (fun y : A => @lem5945532 A s p x y)). Qed.
Lemma lem5945534 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945535 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) : (term429 A s p x) = (term429 A s p x).
Proof. exact (MK_COMB (@lem5945534 A) (@lem5945533 A s p x)). Qed.
Lemma lem5945536 {A : Type'} (s : A -> Prop) (p : A -> A) : (term430 A s p) = (term430 A s p).
Proof. exact (fun_ext (fun x : A => @lem5945535 A s p x)). Qed.
Lemma lem5945537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945538 {A : Type'} (s : A -> Prop) (p : A -> A) : (term57 A s p) = (term57 A s p).
Proof. exact (MK_COMB (@lem5945537 A) (@lem5945536 A s p)). Qed.
Lemma lem5945543 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term98 A s p x y) = (term98 A s p x y).
Proof. exact (eq_refl (term98 A s p x y)). Qed.
Lemma lem5945544 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term99 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5945543 A s p x y)). Qed.
Lemma lem5945545 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem5945546 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term100 A s p y).
Proof. exact (MK_COMB (@lem5945545 A) (@lem5945544 A s p y)). Qed.
Lemma lem5945549 {A : Type'} (y : A) (s : A -> Prop) : (term101 A y s) = (term101 A y s).
Proof. exact (eq_refl (term101 A y s)). Qed.
Lemma lem5945550 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term102 A s p y).
Proof. exact (MK_COMB (@lem5945549 A y s) (@lem5945546 A s p y)). Qed.
Lemma lem5945551 {A : Type'} (s : A -> Prop) (p : A -> A) : (term103 A s p) = (term103 A s p).
Proof. exact (fun_ext (fun y : A => @lem5945550 A s p y)). Qed.
Lemma lem5945552 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945553 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term39 A s p).
Proof. exact (MK_COMB (@lem5945552 A) (@lem5945551 A s p)). Qed.
Lemma lem5945554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945555 {A : Type'} (s : A -> Prop) (p : A -> A) : (term76 A s p) = (term76 A s p).
Proof. exact (MK_COMB (@lem5945554) (@lem5945553 A s p)). Qed.
Lemma lem5945556 {A : Type'} (s : A -> Prop) (p : A -> A) : (term417 A s p) = (term417 A s p).
Proof. exact (MK_COMB (@lem5945555 A s p) (@lem5945538 A s p)). Qed.
Lemma lem5945561 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term104 A p x s) = (term104 A p x s).
Proof. exact (eq_refl (term104 A p x s)). Qed.
Lemma lem5945562 {A : Type'} (p : A -> A) (s : A -> Prop) : (term105 A p s) = (term105 A p s).
Proof. exact (fun_ext (fun x : A => @lem5945561 A p x s)). Qed.
Lemma lem5945563 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945564 {A : Type'} (p : A -> A) (s : A -> Prop) : (term40 A p s) = (term40 A p s).
Proof. exact (MK_COMB (@lem5945563 A) (@lem5945562 A p s)). Qed.
Lemma lem5945565 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5945566 {A : Type'} (p : A -> A) (s : A -> Prop) : (term79 A p s) = (term79 A p s).
Proof. exact (MK_COMB (@lem5945565) (@lem5945564 A p s)). Qed.
Lemma lem5945567 {A : Type'} (s : A -> Prop) (p : A -> A) : (term418 A s p) = (term418 A s p).
Proof. exact (MK_COMB (@lem5945566 A p s) (@lem5945556 A s p)). Qed.
Lemma lem5945568 {A : Type'} (p : A -> A) : (term420 A p) = (term420 A p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5945567 A s p)). Qed.
Lemma lem5945569 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5945570 {A : Type'} (p : A -> A) : (term422 A p) = (term422 A p).
Proof. exact (MK_COMB (@lem5945569 A) (@lem5945568 A p)). Qed.
Lemma lem5945571 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun p : A -> A => @lem5945570 A p)). Qed.
Lemma lem5945572 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem5945573 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (MK_COMB (@lem5945572 A) (@lem5945571 A)). Qed.
Lemma lem5945628 {A : Type'} : (term425 A) = (term426 A).
Proof. exact (TRANS (@lem5945519 A) (@lem5945573 A)). Qed.
Lemma lem5945629 {A : Type'} : (term426 A) = (term425 A).
Proof. exact (SYM (@lem5945628 A)). Qed.
Lemma lem5945630 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term40 A p s.
Proof. exact (h1). Qed.
Lemma lem5945631 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) : term39 A s p.
Proof. exact (h1). Qed.
Lemma lem5945634 (p : Prop) : p = (term67 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5945635 {A : Type'} (x : A) (y : A) : (x = y) = (term431 A x y).
Proof. exact (@lem5945634 (x = y)). Qed.
Lemma lem5945636 {A : Type'} (x : A) (y : A) : (term431 A x y) = (x = y).
Proof. exact (SYM (@lem5945635 A x y)). Qed.
Lemma lem5945637 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term371 A x y.
Proof. exact (h1). Qed.
Lemma lem5945644 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term104 A p x s) = (term108 A p x s).
Proof. exact (@lem17265 (@IN A x s) (term109 A p x s)). Qed.
Lemma lem5945645 {A : Type'} (p : A -> A) (s : A -> Prop) : (term105 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5945644 A p x s)). Qed.
Lemma lem5945646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945699 {A : Type'} (p : A -> A) (s : A -> Prop) : (term40 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5945646 A) (@lem5945645 A p s)). Qed.
Lemma lem5945700 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5945699 A p s) (@lem5945630 A p s h1)). Qed.
Lemma lem5945710 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term112 A s p x y) = (term113 A s p x y).
Proof. exact (@lem17045 (@IN A x s) ((p x) = y)). Qed.
Lemma lem5945715 {A : Type'} (x' : A) (x : A) : (x' = x) = (x' = x).
Proof. exact (eq_refl (x' = x)). Qed.
Lemma lem5945716 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5945717 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term114 A s p y x') = (term98 A s p x' y).
Proof. exact (eq_refl (term114 A s p y x')). Qed.
Lemma lem5945718 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term112 A s p x' y) = (term113 A s p x' y).
Proof. exact (@lem5945710 A s p x' y). Qed.
Lemma lem5945719 {A : Type'} (P : A -> Prop) : (@ex1 A P) = (term115 A P).
Proof. exact (@lem18897 A P). Qed.
Lemma lem5945720 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term116 A s p y).
Proof. exact (@lem5945719 A (term99 A s p y)). Qed.
Lemma lem5945721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5945722 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term117 A s p y x') = (term112 A s p x' y).
Proof. exact (MK_COMB (@lem5945721) (@lem5945717 A s p x' y)). Qed.
Lemma lem5945723 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term117 A s p y x') = (term113 A s p x' y).
Proof. exact (TRANS (@lem5945722 A s p x' y) (@lem5945718 A s p x' y)). Qed.
Lemma lem5945724 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5945725 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A) (y : A) : (term118 A s p y x') = (term119 A s p x' y).
Proof. exact (MK_COMB (@lem5945724) (@lem5945723 A s p x' y)). Qed.
Lemma lem5945726 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term120 A s p y x' x) = (term121 A s p y x' x).
Proof. exact (MK_COMB (@lem5945725 A s p x' y) (@lem5945715 A x' x)). Qed.
Lemma lem5945727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5945728 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term117 A s p y x) = (term112 A s p x y).
Proof. exact (MK_COMB (@lem5945727) (@lem5945716 A s p x y)). Qed.
Lemma lem5945729 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term117 A s p y x) = (term113 A s p x y).
Proof. exact (TRANS (@lem5945728 A s p x y) (@lem5945710 A s p x y)). Qed.
Lemma lem5945730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5945731 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term118 A s p y x) = (term119 A s p x y).
Proof. exact (MK_COMB (@lem5945730) (@lem5945729 A s p x y)). Qed.
Lemma lem5945732 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term122 A s p y x' x) = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5945731 A s p x y) (@lem5945726 A s p y x' x)). Qed.
Lemma lem5945733 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term124 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5945732 A s p y x' x)). Qed.
Lemma lem5945734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945735 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term126 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5945734 A) (@lem5945733 A s p y x)). Qed.
Lemma lem5945736 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term128 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5945735 A s p y x)). Qed.
Lemma lem5945737 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945738 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term130 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5945737 A) (@lem5945736 A s p y)). Qed.
Lemma lem5945739 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5945740 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term132 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5945739 A s p x y)). Qed.
Lemma lem5945741 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5945742 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term133 A s p y) = (term134 A s p y).
Proof. exact (MK_COMB (@lem5945741 A) (@lem5945740 A s p y)). Qed.
Lemma lem5945743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5945744 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term135 A s p y) = (term136 A s p y).
Proof. exact (MK_COMB (@lem5945743) (@lem5945742 A s p y)). Qed.
Lemma lem5945745 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term116 A s p y) = (term137 A s p y).
Proof. exact (MK_COMB (@lem5945744 A s p y) (@lem5945738 A s p y)). Qed.
Lemma lem5945746 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term100 A s p y) = (term137 A s p y).
Proof. exact (TRANS (@lem5945720 A s p y) (@lem5945745 A s p y)). Qed.
Lemma lem5945748 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5945749 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term139 A s p y) = (term140 A s p y).
Proof. exact (MK_COMB (@lem5945748 A y s) (@lem5945746 A s p y)). Qed.
Lemma lem5945750 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term139 A s p y).
Proof. exact (@lem17265 (@IN A y s) (term100 A s p y)). Qed.
Lemma lem5945751 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term102 A s p y) = (term140 A s p y).
Proof. exact (TRANS (@lem5945750 A s p y) (@lem5945749 A s p y)). Qed.
Lemma lem5945752 {A : Type'} (s : A -> Prop) (p : A -> A) : (term103 A s p) = (term141 A s p).
Proof. exact (fun_ext (fun y : A => @lem5945751 A s p y)). Qed.
Lemma lem5945753 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945754 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term142 A s p).
Proof. exact (MK_COMB (@lem5945753 A) (@lem5945752 A s p)). Qed.
Lemma lem5945856 {A : Type'} (P : Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem5945857 {A : Type'} (P : Prop) (Q : A -> Prop) : (term143 A P Q) = (term144 A P Q).
Proof. exact (@lem5945856 A P Q). Qed.
Lemma lem5945858 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term146 A s p y x).
Proof. exact (@lem5945857 A (term113 A s p x y) (term147 A s p y x)). Qed.
Lemma lem5945859 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5945860 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5945861 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term149 A s p y x x') = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5945860 A s p x y) (@lem5945859 A s p y x' x)). Qed.
Lemma lem5945862 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term150 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5945861 A s p y x' x)). Qed.
Lemma lem5945863 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945864 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5945863 A) (@lem5945862 A s p y x)). Qed.
Lemma lem5945865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5945866 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term151 A s p y x) = (term152 A s p y x).
Proof. exact (MK_COMB (@lem5945865) (@lem5945864 A s p y x)). Qed.
Lemma lem5945867 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5945868 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term153 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5945867 A s p y x' x)). Qed.
Lemma lem5945869 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945870 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term154 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5945869 A) (@lem5945868 A s p y x)). Qed.
Lemma lem5945871 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5945872 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5945871 A s p x y) (@lem5945870 A s p y x)). Qed.
Lemma lem5945873 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term145 A s p y x) = (term146 A s p y x)) = ((term127 A s p y x) = (term156 A s p y x)).
Proof. exact (MK_COMB (@lem5945866 A s p y x) (@lem5945872 A s p y x)). Qed.
Lemma lem5945874 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term127 A s p y x) = (term156 A s p y x).
Proof. exact (EQ_MP (@lem5945873 A s p y x) (@lem5945858 A s p y x)). Qed.
Lemma lem5945923 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term129 A s p y) = (term157 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5945874 A s p y x)). Qed.
Lemma lem5945924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945925 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term131 A s p y) = (term158 A s p y).
Proof. exact (MK_COMB (@lem5945924 A) (@lem5945923 A s p y)). Qed.
Lemma lem5945974 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term136 A s p y) = (term136 A s p y).
Proof. exact (eq_refl (term136 A s p y)). Qed.
Lemma lem5945975 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term137 A s p y) = (term159 A s p y).
Proof. exact (MK_COMB (@lem5945974 A s p y) (@lem5945925 A s p y)). Qed.
Lemma lem5945976 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5945977 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term140 A s p y) = (term160 A s p y).
Proof. exact (MK_COMB (@lem5945976 A y s) (@lem5945975 A s p y)). Qed.
Lemma lem5945978 {A : Type'} (s : A -> Prop) (p : A -> A) : (term141 A s p) = (term161 A s p).
Proof. exact (fun_ext (fun y : A => @lem5945977 A s p y)). Qed.
Lemma lem5945979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5945980 {A : Type'} (s : A -> Prop) (p : A -> A) : (term142 A s p) = (term162 A s p).
Proof. exact (MK_COMB (@lem5945979 A) (@lem5945978 A s p)). Qed.
Lemma lem5946030 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5946031 {A : Type'} (P : A -> Prop) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem5946030 A P Q). Qed.
Lemma lem5946032 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term165 A s p y) = (term166 A s p y).
Proof. exact (@lem5946031 A (term99 A s p y) (term158 A s p y)). Qed.
Lemma lem5946033 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5946034 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term132 A s p y) = (term99 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946033 A s p x y)). Qed.
Lemma lem5946035 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5946036 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term133 A s p y) = (term134 A s p y).
Proof. exact (MK_COMB (@lem5946035 A) (@lem5946034 A s p y)). Qed.
Lemma lem5946037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5946038 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term135 A s p y) = (term136 A s p y).
Proof. exact (MK_COMB (@lem5946037) (@lem5946036 A s p y)). Qed.
Lemma lem5946039 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (eq_refl (term158 A s p y)). Qed.
Lemma lem5946040 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term165 A s p y) = (term159 A s p y).
Proof. exact (MK_COMB (@lem5946038 A s p y) (@lem5946039 A s p y)). Qed.
Lemma lem5946041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946042 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term167 A s p y) = (term168 A s p y).
Proof. exact (MK_COMB (@lem5946041) (@lem5946040 A s p y)). Qed.
Lemma lem5946043 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term114 A s p y x) = (term98 A s p x y).
Proof. exact (eq_refl (term114 A s p y x)). Qed.
Lemma lem5946044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5946045 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term169 A s p y x) = (term170 A s p x y).
Proof. exact (MK_COMB (@lem5946044) (@lem5946043 A s p x y)). Qed.
Lemma lem5946046 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (eq_refl (term158 A s p y)). Qed.
Lemma lem5946047 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term171 A x s p y) = (term172 A x s p y).
Proof. exact (MK_COMB (@lem5946045 A s p x y) (@lem5946046 A s p y)). Qed.
Lemma lem5946048 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term173 A s p y) = (term174 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946047 A x s p y)). Qed.
Lemma lem5946049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5946050 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term166 A s p y) = (term175 A s p y).
Proof. exact (MK_COMB (@lem5946049 A) (@lem5946048 A s p y)). Qed.
Lemma lem5946051 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term165 A s p y) = (term166 A s p y)) = ((term159 A s p y) = (term175 A s p y)).
Proof. exact (MK_COMB (@lem5946042 A s p y) (@lem5946050 A s p y)). Qed.
Lemma lem5946052 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term159 A s p y) = (term175 A s p y).
Proof. exact (EQ_MP (@lem5946051 A s p y) (@lem5946032 A s p y)). Qed.
Lemma lem5946053 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946054 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term160 A s p y) = (term176 A s p y).
Proof. exact (MK_COMB (@lem5946053 A y s) (@lem5946052 A s p y)). Qed.
Lemma lem5946056 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5946057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem5946056 A P Q). Qed.
Lemma lem5946058 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term179 A s p y) = (term180 A s p y).
Proof. exact (@lem5946057 A (term181 A y s) (term174 A s p y)). Qed.
Lemma lem5946059 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term182 A s p y x) = (term172 A x s p y).
Proof. exact (eq_refl (term182 A s p y x)). Qed.
Lemma lem5946060 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term183 A s p y) = (term174 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946059 A x s p y)). Qed.
Lemma lem5946061 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5946062 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term184 A s p y) = (term175 A s p y).
Proof. exact (MK_COMB (@lem5946061 A) (@lem5946060 A s p y)). Qed.
Lemma lem5946063 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946064 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term179 A s p y) = (term176 A s p y).
Proof. exact (MK_COMB (@lem5946063 A y s) (@lem5946062 A s p y)). Qed.
Lemma lem5946065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946066 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term185 A s p y) = (term186 A s p y).
Proof. exact (MK_COMB (@lem5946065) (@lem5946064 A s p y)). Qed.
Lemma lem5946067 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term182 A s p y x) = (term172 A x s p y).
Proof. exact (eq_refl (term182 A s p y x)). Qed.
Lemma lem5946068 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946069 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term187 A s p y x) = (term188 A x s p y).
Proof. exact (MK_COMB (@lem5946068 A y s) (@lem5946067 A x s p y)). Qed.
Lemma lem5946070 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term189 A s p y) = (term190 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946069 A x s p y)). Qed.
Lemma lem5946071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5946072 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term180 A s p y) = (term191 A s p y).
Proof. exact (MK_COMB (@lem5946071 A) (@lem5946070 A s p y)). Qed.
Lemma lem5946073 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : ((term179 A s p y) = (term180 A s p y)) = ((term176 A s p y) = (term191 A s p y)).
Proof. exact (MK_COMB (@lem5946066 A s p y) (@lem5946072 A s p y)). Qed.
Lemma lem5946074 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term176 A s p y) = (term191 A s p y).
Proof. exact (EQ_MP (@lem5946073 A s p y) (@lem5946058 A s p y)). Qed.
Lemma lem5946075 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term160 A s p y) = (term191 A s p y).
Proof. exact (TRANS (@lem5946054 A s p y) (@lem5946074 A s p y)). Qed.
Lemma lem5946076 {A : Type'} (s : A -> Prop) (p : A -> A) : (term161 A s p) = (term192 A s p).
Proof. exact (fun_ext (fun y : A => @lem5946075 A s p y)). Qed.
Lemma lem5946077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946078 {A : Type'} (s : A -> Prop) (p : A -> A) : (term162 A s p) = (term193 A s p).
Proof. exact (MK_COMB (@lem5946077 A) (@lem5946076 A s p)). Qed.
Lemma lem5946080 {A B : Type'} (P : type1413 A B) : (term194 A B P) = (term195 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5946081 {A : Type'} (P : type1402 A) : (term196 A P) = (term197 A P).
Proof. exact (@lem5946080 A A P). Qed.
Lemma lem5946082 {A : Type'} (s : A -> Prop) (p : A -> A) : (term198 A s p) = (term199 A s p).
Proof. exact (@lem5946081 A (term200 A s p)). Qed.
Lemma lem5946083 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term201 A s p y) = (term190 A s p y).
Proof. exact (eq_refl (term201 A s p y)). Qed.
Lemma lem5946084 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5946085 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term202 A s p y x) = (term203 A s p y x).
Proof. exact (MK_COMB (@lem5946083 A s p y) (@lem5946084 A x)). Qed.
Lemma lem5946086 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term203 A s p y x) = (term188 A x s p y).
Proof. exact (eq_refl (term203 A s p y x)). Qed.
Lemma lem5946087 {A : Type'} (x : A) (s : A -> Prop) (p : A -> A) (y : A) : (term202 A s p y x) = (term188 A x s p y).
Proof. exact (TRANS (@lem5946085 A s p y x) (@lem5946086 A x s p y)). Qed.
Lemma lem5946088 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term204 A s p y) = (term190 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946087 A x s p y)). Qed.
Lemma lem5946089 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5946090 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term205 A s p y) = (term191 A s p y).
Proof. exact (MK_COMB (@lem5946089 A) (@lem5946088 A s p y)). Qed.
Lemma lem5946091 {A : Type'} (s : A -> Prop) (p : A -> A) : (term206 A s p) = (term192 A s p).
Proof. exact (fun_ext (fun y : A => @lem5946090 A s p y)). Qed.
Lemma lem5946092 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946093 {A : Type'} (s : A -> Prop) (p : A -> A) : (term198 A s p) = (term193 A s p).
Proof. exact (MK_COMB (@lem5946092 A) (@lem5946091 A s p)). Qed.
Lemma lem5946094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946095 {A : Type'} (s : A -> Prop) (p : A -> A) : (term207 A s p) = (term208 A s p).
Proof. exact (MK_COMB (@lem5946094) (@lem5946093 A s p)). Qed.
Lemma lem5946096 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term201 A s p y) = (term190 A s p y).
Proof. exact (eq_refl (term201 A s p y)). Qed.
Lemma lem5946097 {A : Type'} (x : A -> A) (y : A) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5946098 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A -> A) (y : A) : (term209 A s p x y) = (term210 A s p x y).
Proof. exact (MK_COMB (@lem5946096 A s p y) (@lem5946097 A x y)). Qed.
Lemma lem5946099 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term210 A s p x y) = (term211 A x s p y).
Proof. exact (eq_refl (term210 A s p x y)). Qed.
Lemma lem5946100 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term209 A s p x y) = (term211 A x s p y).
Proof. exact (TRANS (@lem5946098 A s p x y) (@lem5946099 A x s p y)). Qed.
Lemma lem5946101 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) : (term212 A s p x) = (term213 A x s p).
Proof. exact (fun_ext (fun y : A => @lem5946100 A x s p y)). Qed.
Lemma lem5946102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946103 {A : Type'} (x : A -> A) (s : A -> Prop) (p : A -> A) : (term214 A s p x) = (term215 A x s p).
Proof. exact (MK_COMB (@lem5946102 A) (@lem5946101 A x s p)). Qed.
Lemma lem5946104 {A : Type'} (s : A -> Prop) (p : A -> A) : (term216 A s p) = (term217 A s p).
Proof. exact (fun_ext (fun x : A -> A => @lem5946103 A x s p)). Qed.
Lemma lem5946105 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem5946106 {A : Type'} (s : A -> Prop) (p : A -> A) : (term199 A s p) = (term218 A s p).
Proof. exact (MK_COMB (@lem5946105 A) (@lem5946104 A s p)). Qed.
Lemma lem5946107 {A : Type'} (s : A -> Prop) (p : A -> A) : ((term198 A s p) = (term199 A s p)) = ((term193 A s p) = (term218 A s p)).
Proof. exact (MK_COMB (@lem5946095 A s p) (@lem5946106 A s p)). Qed.
Lemma lem5946108 {A : Type'} (s : A -> Prop) (p : A -> A) : (term193 A s p) = (term218 A s p).
Proof. exact (EQ_MP (@lem5946107 A s p) (@lem5946082 A s p)). Qed.
Lemma lem5946109 {A : Type'} (s : A -> Prop) (p : A -> A) : (term162 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5946078 A s p) (@lem5946108 A s p)). Qed.
Lemma lem5946110 {A : Type'} (s : A -> Prop) (p : A -> A) : (term142 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5945980 A s p) (@lem5946109 A s p)). Qed.
Lemma lem5946111 {A : Type'} (s : A -> Prop) (p : A -> A) : (term39 A s p) = (term218 A s p).
Proof. exact (TRANS (@lem5945754 A s p) (@lem5946110 A s p)). Qed.
Lemma lem5946112 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) : term218 A s p.
Proof. exact (EQ_MP (@lem5946111 A s p) (@lem5945631 A s p h1)). Qed.
Lemma lem5946126 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term432 A s x p y.
Proof. exact (h1). Qed.
Lemma lem5946132 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term371 A x y.
Proof. exact (h1). Qed.
Lemma lem5946133 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term215 A x' s p.
Proof. exact (h1). Qed.
Lemma lem5946150 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term108 A p x s) = (term108 A p x s).
Proof. exact (eq_refl (term108 A p x s)). Qed.
Lemma lem5946151 {A : Type'} (p : A -> A) (s : A -> Prop) : (term110 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5946150 A p x s)). Qed.
Lemma lem5946152 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946153 {A : Type'} (p : A -> A) (s : A -> Prop) : (term111 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5946152 A) (@lem5946151 A p s)). Qed.
Lemma lem5946154 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5946153 A p s) (@lem5945700 A p s h1)). Qed.
Lemma lem5946180 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term432 A s x p y.
Proof. exact (h1). Qed.
Lemma lem5946188 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term371 A x y.
Proof. exact (h1). Qed.
Lemma lem5946215 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term121 A s p y x' x) = (term121 A s p y x' x).
Proof. exact (eq_refl (term121 A s p y x' x)). Qed.
Lemma lem5946216 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term147 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5946215 A s p y x' x)). Qed.
Lemma lem5946217 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946218 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term155 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5946217 A) (@lem5946216 A s p y x)). Qed.
Lemma lem5946239 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5946240 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term156 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5946239 A s p x y) (@lem5946218 A s p y x)). Qed.
Lemma lem5946241 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term157 A s p y) = (term157 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946240 A s p y x)). Qed.
Lemma lem5946242 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946243 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term158 A s p y).
Proof. exact (MK_COMB (@lem5946242 A) (@lem5946241 A s p y)). Qed.
Lemma lem5946264 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946265 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x' s p y) = (term266 A x' s p y).
Proof. exact (MK_COMB (@lem5946264 A s p x' y) (@lem5946243 A s p y)). Qed.
Lemma lem5946274 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946275 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x' s p y) = (term211 A x' s p y).
Proof. exact (MK_COMB (@lem5946274 A y s) (@lem5946265 A x' s p y)). Qed.
Lemma lem5946276 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term213 A x' s p) = (term213 A x' s p).
Proof. exact (fun_ext (fun y : A => @lem5946275 A x' s p y)). Qed.
Lemma lem5946277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946278 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x' s p) = (term215 A x' s p).
Proof. exact (MK_COMB (@lem5946277 A) (@lem5946276 A x' s p)). Qed.
Lemma lem5946279 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term215 A x' s p.
Proof. exact (EQ_MP (@lem5946278 A x' s p) (@lem5946133 A x' s p h1)). Qed.
Lemma lem5946280 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term433 A s x p y.
Proof. exact (proj2 (@lem5946180 A s x p y h1)). Qed.
Lemma lem5946291 {A : Type'} (p : A -> A) (x : A) (s : A -> Prop) : (term108 A p x s) = (term108 A p x s).
Proof. exact (eq_refl (term108 A p x s)). Qed.
Lemma lem5946292 {A : Type'} (p : A -> A) (s : A -> Prop) : (term110 A p s) = (term110 A p s).
Proof. exact (fun_ext (fun x : A => @lem5946291 A p x s)). Qed.
Lemma lem5946293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946295 {A : Type'} (p : A -> A) (s : A -> Prop) : (term111 A p s) = (term111 A p s).
Proof. exact (MK_COMB (@lem5946293 A) (@lem5946292 A p s)). Qed.
Lemma lem5946296 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term111 A p s.
Proof. exact (EQ_MP (@lem5946295 A p s) (@lem5946154 A p s h1)). Qed.
Lemma lem5946300 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term371 A x y.
Proof. exact (h1). Qed.
Lemma lem5946302 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5946303 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5946302 A P Q). Qed.
Lemma lem5946304 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term145 A s p y x).
Proof. exact (@lem5946303 A (term113 A s p x y) (term147 A s p y x)). Qed.
Lemma lem5946305 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5946306 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term153 A s p y x) = (term147 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5946305 A s p y x' x)). Qed.
Lemma lem5946307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946308 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term154 A s p y x) = (term155 A s p y x).
Proof. exact (MK_COMB (@lem5946307 A) (@lem5946306 A s p y x)). Qed.
Lemma lem5946309 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5946310 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term146 A s p y x) = (term156 A s p y x).
Proof. exact (MK_COMB (@lem5946309 A s p x y) (@lem5946308 A s p y x)). Qed.
Lemma lem5946311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946312 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term267 A s p y x) = (term268 A s p y x).
Proof. exact (MK_COMB (@lem5946311) (@lem5946310 A s p y x)). Qed.
Lemma lem5946313 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term148 A s p y x x') = (term121 A s p y x' x).
Proof. exact (eq_refl (term148 A s p y x x')). Qed.
Lemma lem5946314 {A : Type'} (s : A -> Prop) (p : A -> A) (x : A) (y : A) : (term119 A s p x y) = (term119 A s p x y).
Proof. exact (eq_refl (term119 A s p x y)). Qed.
Lemma lem5946315 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term149 A s p y x x') = (term123 A s p y x' x).
Proof. exact (MK_COMB (@lem5946314 A s p x y) (@lem5946313 A s p y x' x)). Qed.
Lemma lem5946316 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term150 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5946315 A s p y x' x)). Qed.
Lemma lem5946317 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946318 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term145 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5946317 A) (@lem5946316 A s p y x)). Qed.
Lemma lem5946319 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term146 A s p y x) = (term145 A s p y x)) = ((term156 A s p y x) = (term127 A s p y x)).
Proof. exact (MK_COMB (@lem5946312 A s p y x) (@lem5946318 A s p y x)). Qed.
Lemma lem5946320 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term156 A s p y x) = (term127 A s p y x).
Proof. exact (EQ_MP (@lem5946319 A s p y x) (@lem5946304 A s p y x)). Qed.
Lemma lem5946321 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term157 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946320 A s p y x)). Qed.
Lemma lem5946322 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946323 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term158 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5946322 A) (@lem5946321 A s p y)). Qed.
Lemma lem5946324 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946325 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x' s p y) = (term269 A x' s p y).
Proof. exact (MK_COMB (@lem5946324 A s p x' y) (@lem5946323 A s p y)). Qed.
Lemma lem5946327 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5946328 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem5946327 A P Q). Qed.
Lemma lem5946329 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term272 A x' s p y) = (term273 A x' s p y).
Proof. exact (@lem5946328 A (term274 A s p x' y) (term129 A s p y)). Qed.
Lemma lem5946330 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term275 A s p y x) = (term127 A s p y x).
Proof. exact (eq_refl (term275 A s p y x)). Qed.
Lemma lem5946331 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term276 A s p y) = (term129 A s p y).
Proof. exact (fun_ext (fun x : A => @lem5946330 A s p y x)). Qed.
Lemma lem5946332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946333 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) : (term277 A s p y) = (term131 A s p y).
Proof. exact (MK_COMB (@lem5946332 A) (@lem5946331 A s p y)). Qed.
Lemma lem5946334 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946335 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term272 A x' s p y) = (term269 A x' s p y).
Proof. exact (MK_COMB (@lem5946334 A s p x' y) (@lem5946333 A s p y)). Qed.
Lemma lem5946336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946337 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term278 A x' s p y) = (term279 A x' s p y).
Proof. exact (MK_COMB (@lem5946336) (@lem5946335 A x' s p y)). Qed.
Lemma lem5946338 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term275 A s p y x) = (term127 A s p y x).
Proof. exact (eq_refl (term275 A s p y x)). Qed.
Lemma lem5946339 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946340 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term280 A x' s p y x) = (term281 A x' s p y x).
Proof. exact (MK_COMB (@lem5946339 A s p x' y) (@lem5946338 A s p y x)). Qed.
Lemma lem5946341 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term282 A x' s p y) = (term283 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946340 A x' s p y x)). Qed.
Lemma lem5946342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946343 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term273 A x' s p y) = (term284 A x' s p y).
Proof. exact (MK_COMB (@lem5946342 A) (@lem5946341 A x' s p y)). Qed.
Lemma lem5946344 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : ((term272 A x' s p y) = (term273 A x' s p y)) = ((term269 A x' s p y) = (term284 A x' s p y)).
Proof. exact (MK_COMB (@lem5946337 A x' s p y) (@lem5946343 A x' s p y)). Qed.
Lemma lem5946345 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term269 A x' s p y) = (term284 A x' s p y).
Proof. exact (EQ_MP (@lem5946344 A x' s p y) (@lem5946329 A x' s p y)). Qed.
Lemma lem5946347 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5946348 {A : Type'} (P : Prop) (Q : A -> Prop) : (term270 A P Q) = (term271 A P Q).
Proof. exact (@lem5946347 A P Q). Qed.
Lemma lem5946349 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term285 A x' s p y x) = (term286 A x' s p y x).
Proof. exact (@lem5946348 A (term274 A s p x' y) (term125 A s p y x)). Qed.
Lemma lem5946350 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term287 A s p y x x') = (term123 A s p y x' x).
Proof. exact (eq_refl (term287 A s p y x x')). Qed.
Lemma lem5946351 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term288 A s p y x) = (term125 A s p y x).
Proof. exact (fun_ext (fun x' : A => @lem5946350 A s p y x' x)). Qed.
Lemma lem5946352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946353 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term289 A s p y x) = (term127 A s p y x).
Proof. exact (MK_COMB (@lem5946352 A) (@lem5946351 A s p y x)). Qed.
Lemma lem5946354 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946355 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term285 A x' s p y x) = (term281 A x' s p y x).
Proof. exact (MK_COMB (@lem5946354 A s p x' y) (@lem5946353 A s p y x)). Qed.
Lemma lem5946356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946357 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term290 A x' s p y x) = (term291 A x' s p y x).
Proof. exact (MK_COMB (@lem5946356) (@lem5946355 A x' s p y x)). Qed.
Lemma lem5946358 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term287 A s p y x x') = (term123 A s p y x' x).
Proof. exact (eq_refl (term287 A s p y x x')). Qed.
Lemma lem5946359 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term265 A s p x' y) = (term265 A s p x' y).
Proof. exact (eq_refl (term265 A s p x' y)). Qed.
Lemma lem5946360 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term292 A x' s p y x x'') = (term293 A x' s p y x'' x).
Proof. exact (MK_COMB (@lem5946359 A s p x' y) (@lem5946358 A s p y x'' x)). Qed.
Lemma lem5946361 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term294 A x' s p y x) = (term295 A x' s p y x).
Proof. exact (fun_ext (fun x'' : A => @lem5946360 A x' s p y x'' x)). Qed.
Lemma lem5946362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946363 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term286 A x' s p y x) = (term296 A x' s p y x).
Proof. exact (MK_COMB (@lem5946362 A) (@lem5946361 A x' s p y x)). Qed.
Lemma lem5946364 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term285 A x' s p y x) = (term286 A x' s p y x)) = ((term281 A x' s p y x) = (term296 A x' s p y x)).
Proof. exact (MK_COMB (@lem5946357 A x' s p y x) (@lem5946363 A x' s p y x)). Qed.
Lemma lem5946365 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term281 A x' s p y x) = (term296 A x' s p y x).
Proof. exact (EQ_MP (@lem5946364 A x' s p y x) (@lem5946349 A x' s p y x)). Qed.
Lemma lem5946366 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term283 A x' s p y) = (term297 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946365 A x' s p y x)). Qed.
Lemma lem5946367 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946368 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term284 A x' s p y) = (term298 A x' s p y).
Proof. exact (MK_COMB (@lem5946367 A) (@lem5946366 A x' s p y)). Qed.
Lemma lem5946369 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term269 A x' s p y) = (term298 A x' s p y).
Proof. exact (TRANS (@lem5946345 A x' s p y) (@lem5946368 A x' s p y)). Qed.
Lemma lem5946370 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term266 A x' s p y) = (term298 A x' s p y).
Proof. exact (TRANS (@lem5946325 A x' s p y) (@lem5946369 A x' s p y)). Qed.
Lemma lem5946371 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946372 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x' s p y) = (term299 A x' s p y).
Proof. exact (MK_COMB (@lem5946371 A y s) (@lem5946370 A x' s p y)). Qed.
Lemma lem5946374 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5946375 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5946374 A P Q). Qed.
Lemma lem5946376 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term300 A x' s p y) = (term301 A x' s p y).
Proof. exact (@lem5946375 A (term181 A y s) (term297 A x' s p y)). Qed.
Lemma lem5946377 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term302 A x' s p y x) = (term296 A x' s p y x).
Proof. exact (eq_refl (term302 A x' s p y x)). Qed.
Lemma lem5946378 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term303 A x' s p y) = (term297 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946377 A x' s p y x)). Qed.
Lemma lem5946379 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946380 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term304 A x' s p y) = (term298 A x' s p y).
Proof. exact (MK_COMB (@lem5946379 A) (@lem5946378 A x' s p y)). Qed.
Lemma lem5946381 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946382 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term300 A x' s p y) = (term299 A x' s p y).
Proof. exact (MK_COMB (@lem5946381 A y s) (@lem5946380 A x' s p y)). Qed.
Lemma lem5946383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946384 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term305 A x' s p y) = (term306 A x' s p y).
Proof. exact (MK_COMB (@lem5946383) (@lem5946382 A x' s p y)). Qed.
Lemma lem5946385 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term302 A x' s p y x) = (term296 A x' s p y x).
Proof. exact (eq_refl (term302 A x' s p y x)). Qed.
Lemma lem5946386 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946387 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term307 A x' s p y x) = (term308 A x' s p y x).
Proof. exact (MK_COMB (@lem5946386 A y s) (@lem5946385 A x' s p y x)). Qed.
Lemma lem5946388 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term309 A x' s p y) = (term310 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946387 A x' s p y x)). Qed.
Lemma lem5946389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946390 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term301 A x' s p y) = (term311 A x' s p y).
Proof. exact (MK_COMB (@lem5946389 A) (@lem5946388 A x' s p y)). Qed.
Lemma lem5946391 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : ((term300 A x' s p y) = (term301 A x' s p y)) = ((term299 A x' s p y) = (term311 A x' s p y)).
Proof. exact (MK_COMB (@lem5946384 A x' s p y) (@lem5946390 A x' s p y)). Qed.
Lemma lem5946392 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term299 A x' s p y) = (term311 A x' s p y).
Proof. exact (EQ_MP (@lem5946391 A x' s p y) (@lem5946376 A x' s p y)). Qed.
Lemma lem5946394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5946395 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term143 A P Q).
Proof. exact (@lem5946394 A P Q). Qed.
Lemma lem5946396 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A x' s p y x) = (term313 A x' s p y x).
Proof. exact (@lem5946395 A (term181 A y s) (term295 A x' s p y x)). Qed.
Lemma lem5946397 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term314 A x' s p y x x'') = (term293 A x' s p y x'' x).
Proof. exact (eq_refl (term314 A x' s p y x x'')). Qed.
Lemma lem5946398 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term315 A x' s p y x) = (term295 A x' s p y x).
Proof. exact (fun_ext (fun x'' : A => @lem5946397 A x' s p y x'' x)). Qed.
Lemma lem5946399 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946400 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term316 A x' s p y x) = (term296 A x' s p y x).
Proof. exact (MK_COMB (@lem5946399 A) (@lem5946398 A x' s p y x)). Qed.
Lemma lem5946401 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946402 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term312 A x' s p y x) = (term308 A x' s p y x).
Proof. exact (MK_COMB (@lem5946401 A y s) (@lem5946400 A x' s p y x)). Qed.
Lemma lem5946403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946404 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term317 A x' s p y x) = (term318 A x' s p y x).
Proof. exact (MK_COMB (@lem5946403) (@lem5946402 A x' s p y x)). Qed.
Lemma lem5946405 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term314 A x' s p y x x'') = (term293 A x' s p y x'' x).
Proof. exact (eq_refl (term314 A x' s p y x x'')). Qed.
Lemma lem5946406 {A : Type'} (y : A) (s : A -> Prop) : (term138 A y s) = (term138 A y s).
Proof. exact (eq_refl (term138 A y s)). Qed.
Lemma lem5946407 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term319 A x' s p y x x'') = (term320 A x' s p y x'' x).
Proof. exact (MK_COMB (@lem5946406 A y s) (@lem5946405 A x' s p y x'' x)). Qed.
Lemma lem5946408 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term321 A x' s p y x) = (term322 A x' s p y x).
Proof. exact (fun_ext (fun x'' : A => @lem5946407 A x' s p y x'' x)). Qed.
Lemma lem5946409 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946410 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term313 A x' s p y x) = (term323 A x' s p y x).
Proof. exact (MK_COMB (@lem5946409 A) (@lem5946408 A x' s p y x)). Qed.
Lemma lem5946411 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : ((term312 A x' s p y x) = (term313 A x' s p y x)) = ((term308 A x' s p y x) = (term323 A x' s p y x)).
Proof. exact (MK_COMB (@lem5946404 A x' s p y x) (@lem5946410 A x' s p y x)). Qed.
Lemma lem5946412 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term308 A x' s p y x) = (term323 A x' s p y x).
Proof. exact (EQ_MP (@lem5946411 A x' s p y x) (@lem5946396 A x' s p y x)). Qed.
Lemma lem5946413 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term310 A x' s p y) = (term324 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946412 A x' s p y x)). Qed.
Lemma lem5946414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946415 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term311 A x' s p y) = (term325 A x' s p y).
Proof. exact (MK_COMB (@lem5946414 A) (@lem5946413 A x' s p y)). Qed.
Lemma lem5946416 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term299 A x' s p y) = (term325 A x' s p y).
Proof. exact (TRANS (@lem5946392 A x' s p y) (@lem5946415 A x' s p y)). Qed.
Lemma lem5946417 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term211 A x' s p y) = (term325 A x' s p y).
Proof. exact (TRANS (@lem5946372 A x' s p y) (@lem5946416 A x' s p y)). Qed.
Lemma lem5946418 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term213 A x' s p) = (term326 A x' s p).
Proof. exact (fun_ext (fun y : A => @lem5946417 A x' s p y)). Qed.
Lemma lem5946419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946420 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x' s p) = (term327 A x' s p).
Proof. exact (MK_COMB (@lem5946419 A) (@lem5946418 A x' s p)). Qed.
Lemma lem5946458 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term320 A x' s p y x'' x) = (term328 A x' s p y x'' x).
Proof. exact (@lem19490 (term274 A s p x' y) (term181 A y s) (term123 A s p y x'' x)). Qed.
Lemma lem5946459 {A : Type'} (s : A -> Prop) (p : A -> A) (y : A) (x' : A) (x : A) : (term329 A s p y x' x) = (term329 A s p y x' x).
Proof. exact (eq_refl (term329 A s p y x' x)). Qed.
Lemma lem5946466 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term330 A s p x' y) = (term331 A s p x' y).
Proof. exact (@lem19490 (term109 A x' y s) (term181 A y s) ((term332 A p x' y) = y)). Qed.
Lemma lem5946467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5946468 {A : Type'} (s : A -> Prop) (p : A -> A) (x' : A -> A) (y : A) : (term333 A s p x' y) = (term334 A s p x' y).
Proof. exact (MK_COMB (@lem5946467) (@lem5946466 A s p x' y)). Qed.
Lemma lem5946469 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term328 A x' s p y x'' x) = (term335 A x' s p y x'' x).
Proof. exact (MK_COMB (@lem5946468 A s p x' y) (@lem5946459 A s p y x'' x)). Qed.
Lemma lem5946471 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x'' : A) (x : A) : (term320 A x' s p y x'' x) = (term335 A x' s p y x'' x).
Proof. exact (TRANS (@lem5946458 A x' s p y x'' x) (@lem5946469 A x' s p y x'' x)). Qed.
Lemma lem5946472 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term322 A x' s p y x) = (term336 A x' s p y x).
Proof. exact (fun_ext (fun x'' : A => @lem5946471 A x' s p y x'' x)). Qed.
Lemma lem5946473 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946474 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) (x : A) : (term323 A x' s p y x) = (term337 A x' s p y x).
Proof. exact (MK_COMB (@lem5946473 A) (@lem5946472 A x' s p y x)). Qed.
Lemma lem5946475 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term324 A x' s p y) = (term338 A x' s p y).
Proof. exact (fun_ext (fun x : A => @lem5946474 A x' s p y x)). Qed.
Lemma lem5946476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946477 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (y : A) : (term325 A x' s p y) = (term339 A x' s p y).
Proof. exact (MK_COMB (@lem5946476 A) (@lem5946475 A x' s p y)). Qed.
Lemma lem5946478 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term326 A x' s p) = (term340 A x' s p).
Proof. exact (fun_ext (fun y : A => @lem5946477 A x' s p y)). Qed.
Lemma lem5946479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5946480 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term327 A x' s p) = (term341 A x' s p).
Proof. exact (MK_COMB (@lem5946479 A) (@lem5946478 A x' s p)). Qed.
Lemma lem5946481 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) : (term215 A x' s p) = (term341 A x' s p).
Proof. exact (TRANS (@lem5946420 A x' s p) (@lem5946480 A x' s p)). Qed.
Lemma lem5946482 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term341 A x' s p.
Proof. exact (EQ_MP (@lem5946481 A x' s p) (@lem5946279 A x' s p h1)). Qed.
Lemma lem5946495 {A : Type'} (_75178 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term346 A p s _75178.
Proof. exact (@lem5946296 A p s h1 _75178). Qed.
Lemma lem5946496 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term346 A p s _75178) = (term108 A p _75178 s).
Proof. exact (eq_refl (term346 A p s _75178)). Qed.
Lemma lem5946498 {A : Type'} (_75179 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term342 A x' s p _75179.
Proof. exact (@lem5946482 A x' s p h1 _75179). Qed.
Lemma lem5946499 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (_75179 : A) : (term342 A x' s p _75179) = (term339 A x' s p _75179).
Proof. exact (eq_refl (term342 A x' s p _75179)). Qed.
Lemma lem5946500 {A : Type'} (_75179 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term339 A x' s p _75179.
Proof. exact (EQ_MP (@lem5946499 A x' s p _75179) (@lem5946498 A _75179 x' s p h1)). Qed.
Lemma lem5946501 {A : Type'} (_75179 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term343 A x' s p _75179 _75180.
Proof. exact (@lem5946500 A _75179 x' s p h1 _75180). Qed.
Lemma lem5946502 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (_75179 : A) (_75180 : A) : (term343 A x' s p _75179 _75180) = (term337 A x' s p _75179 _75180).
Proof. exact (eq_refl (term343 A x' s p _75179 _75180)). Qed.
Lemma lem5946503 {A : Type'} (_75179 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term337 A x' s p _75179 _75180.
Proof. exact (EQ_MP (@lem5946502 A x' s p _75179 _75180) (@lem5946501 A _75179 _75180 x' s p h1)). Qed.
Lemma lem5946504 {A : Type'} (_75179 : A) (_75180 : A) (_75181 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term344 A x' s p _75179 _75180 _75181.
Proof. exact (@lem5946503 A _75179 _75180 x' s p h1 _75181). Qed.
Lemma lem5946505 {A : Type'} (x' : A -> A) (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term344 A x' s p _75179 _75180 _75181) = (term335 A x' s p _75179 _75181 _75180).
Proof. exact (eq_refl (term344 A x' s p _75179 _75180 _75181)). Qed.
Lemma lem5946506 {A : Type'} (_75179 : A) (_75181 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term335 A x' s p _75179 _75181 _75180.
Proof. exact (EQ_MP (@lem5946505 A x' s p _75179 _75181 _75180) (@lem5946504 A _75179 _75180 _75181 x' s p h1)). Qed.
Lemma lem5946507 {A : Type'} (_75179 : A) (_75181 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term329 A s p _75179 _75181 _75180.
Proof. exact (proj2 (@lem5946506 A _75179 _75181 _75180 x' s p h1)). Qed.
Lemma lem5946516 {A : Type'} (_75178 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term108 A p _75178 s.
Proof. exact (EQ_MP (@lem5946496 A p _75178 s) (@lem5946495 A _75178 p s h1)). Qed.
Lemma lem5946518 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term371 A x y.
Proof. exact (h1). Qed.
Lemma lem5946535 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term121 A s p _75179 _75181 _75180) = (term434 A s p _75179 _75181 _75180).
Proof. exact (@lem5942965 (term181 A _75181 s) (term435 A p _75181 _75179) (_75181 = _75180)). Qed.
Lemma lem5946536 {A : Type'} (s : A -> Prop) (p : A -> A) (_75180 : A) (_75179 : A) : (term119 A s p _75180 _75179) = (term119 A s p _75180 _75179).
Proof. exact (eq_refl (term119 A s p _75180 _75179)). Qed.
Lemma lem5946537 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term123 A s p _75179 _75181 _75180) = (term436 A s p _75179 _75181 _75180).
Proof. exact (MK_COMB (@lem5946536 A s p _75180 _75179) (@lem5946535 A s p _75179 _75181 _75180)). Qed.
Lemma lem5946544 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term436 A s p _75179 _75181 _75180) = (term437 A s p _75179 _75181 _75180).
Proof. exact (@lem5942965 (term181 A _75180 s) (term435 A p _75180 _75179) (term434 A s p _75179 _75181 _75180)). Qed.
Lemma lem5946545 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term123 A s p _75179 _75181 _75180) = (term437 A s p _75179 _75181 _75180).
Proof. exact (TRANS (@lem5946537 A s p _75179 _75181 _75180) (@lem5946544 A s p _75179 _75181 _75180)). Qed.
Lemma lem5946546 {A : Type'} (_75179 : A) (s : A -> Prop) : (term138 A _75179 s) = (term138 A _75179 s).
Proof. exact (eq_refl (term138 A _75179 s)). Qed.
Lemma lem5946549 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term329 A s p _75179 _75181 _75180) = (term438 A s p _75179 _75181 _75180).
Proof. exact (MK_COMB (@lem5946546 A _75179 s) (@lem5946545 A s p _75179 _75181 _75180)). Qed.
Lemma lem5946550 {A : Type'} (_75179 : A) (_75181 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term438 A s p _75179 _75181 _75180.
Proof. exact (EQ_MP (@lem5946549 A s p _75179 _75181 _75180) (@lem5946507 A _75179 _75181 _75180 x' s p h1)). Qed.
Lemma lem5946603 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A y s.
Proof. exact (proj1 (@lem5946280 A s x p y h1)). Qed.
Lemma lem5946604 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term355 A y s.
Proof. exact (fun h0 : term181 A y s => @lem5946603 A s x p y h1). Qed.
Lemma lem5946606 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946607 {A : Type'} (y : A) (s : A -> Prop) : (term355 A y s) = (@IN A y s).
Proof. exact (@lem5946606 (@IN A y s)). Qed.
Lemma lem5946608 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A y s.
Proof. exact (EQ_MP (@lem5946607 A y s) (@lem5946604 A s x p y h1)). Qed.
Lemma lem5946614 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5946615 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term108 A p _75178 s) = (term394 A p _75178 s).
Proof. exact (@lem5946614 (term109 A p _75178 s) (term181 A _75178 s)). Qed.
Lemma lem5946621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946622 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term395 A p _75178 s) = (term396 A p _75178 s).
Proof. exact (MK_COMB (@lem5946621) (@lem5946615 A p _75178 s)). Qed.
Lemma lem5946628 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term394 A p _75178 s) = (term394 A p _75178 s).
Proof. exact (eq_refl (term394 A p _75178 s)). Qed.
Lemma lem5946629 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : ((term108 A p _75178 s) = (term394 A p _75178 s)) = ((term394 A p _75178 s) = (term394 A p _75178 s)).
Proof. exact (MK_COMB (@lem5946622 A p _75178 s) (@lem5946628 A p _75178 s)). Qed.
Lemma lem5946631 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5946632 (x : Prop) : (x = x) = True.
Proof. exact (@lem5946631 Prop x). Qed.
Lemma lem5946633 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : ((term394 A p _75178 s) = (term394 A p _75178 s)) = True.
Proof. exact (@lem5946632 (term394 A p _75178 s)). Qed.
Lemma lem5946634 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : ((term108 A p _75178 s) = (term394 A p _75178 s)) = True.
Proof. exact (TRANS (@lem5946629 A p _75178 s) (@lem5946633 A p _75178 s)). Qed.
Lemma lem5946635 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : True = ((term108 A p _75178 s) = (term394 A p _75178 s)).
Proof. exact (SYM (@lem5946634 A p _75178 s)). Qed.
Lemma lem5946636 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term108 A p _75178 s) = (term394 A p _75178 s).
Proof. exact (EQ_MP (@lem5946635 A p _75178 s) (@lem0)). Qed.
Lemma lem5946637 {A : Type'} (_75178 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term394 A p _75178 s.
Proof. exact (EQ_MP (@lem5946636 A p _75178 s) (@lem5946516 A _75178 p s h1)). Qed.
Lemma lem5946639 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5946640 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term394 A p _75178 s) = (term397 A p _75178 s).
Proof. exact (@lem5946639 (term181 A _75178 s) (term109 A p _75178 s)). Qed.
Lemma lem5946642 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5946643 {A : Type'} (_75178 : A) (s : A -> Prop) : (term362 A _75178 s) = (@IN A _75178 s).
Proof. exact (@lem5946642 (@IN A _75178 s)). Qed.
Lemma lem5946644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5946645 {A : Type'} (_75178 : A) (s : A -> Prop) : (term363 A _75178 s) = (term101 A _75178 s).
Proof. exact (MK_COMB (@lem5946644) (@lem5946643 A _75178 s)). Qed.
Lemma lem5946646 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term109 A p _75178 s) = (term109 A p _75178 s).
Proof. exact (eq_refl (term109 A p _75178 s)). Qed.
Lemma lem5946647 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term397 A p _75178 s) = (term104 A p _75178 s).
Proof. exact (MK_COMB (@lem5946645 A _75178 s) (@lem5946646 A p _75178 s)). Qed.
Lemma lem5946648 {A : Type'} (p : A -> A) (_75178 : A) (s : A -> Prop) : (term394 A p _75178 s) = (term104 A p _75178 s).
Proof. exact (TRANS (@lem5946640 A p _75178 s) (@lem5946647 A p _75178 s)). Qed.
Lemma lem5946651 {A : Type'} (_75178 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p _75178 s.
Proof. exact (EQ_MP (@lem5946648 A p _75178 s) (@lem5946637 A _75178 p s h1)). Qed.
Lemma lem5946652 {A : Type'} (_75178 : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p _75178 s.
Proof. exact (@lem5946651 A _75178 p s h1). Qed.
Lemma lem5946653 {A : Type'} (y : A) (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term104 A p y s.
Proof. exact (@lem5946652 A y p s h1). Qed.
Lemma lem5946656 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term432 A s x p y) : term109 A p y s.
Proof. exact (@lem5946653 A y p s h1 (@lem5946608 A s x p y h2)). Qed.
Lemma lem5946657 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term432 A s x p y) : term398 A p y s.
Proof. exact (fun h0 : term351 A p y s => @lem5946656 A s x p y h1 h2). Qed.
Lemma lem5946659 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946660 {A : Type'} (p : A -> A) (y : A) (s : A -> Prop) : (term398 A p y s) = (term109 A p y s).
Proof. exact (@lem5946659 (term109 A p y s)). Qed.
Lemma lem5946661 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term432 A s x p y) : term109 A p y s.
Proof. exact (EQ_MP (@lem5946660 A p y s) (@lem5946657 A s x p y h1 h2)). Qed.
Lemma lem5946663 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A y s.
Proof. exact (proj1 (@lem5946280 A s x p y h1)). Qed.
Lemma lem5946664 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term355 A y s.
Proof. exact (fun h0 : term181 A y s => @lem5946663 A s x p y h1). Qed.
Lemma lem5946666 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946667 {A : Type'} (y : A) (s : A -> Prop) : (term355 A y s) = (@IN A y s).
Proof. exact (@lem5946666 (@IN A y s)). Qed.
Lemma lem5946668 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A y s.
Proof. exact (EQ_MP (@lem5946667 A y s) (@lem5946664 A s x p y h1)). Qed.
Lemma lem5946670 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem5946671 {A : Type'} (x : A) : x = x.
Proof. exact (@lem5946670 A x). Qed.
Lemma lem5946672 {A : Type'} (p : A -> A) (y : A) : (p y) = (p y).
Proof. exact (@lem5946671 A (p y)). Qed.
Lemma lem5946673 {A : Type'} (p : A -> A) (y : A) : term439 A p y.
Proof. exact (fun h0 : term440 A p y => @lem5946672 A p y). Qed.
Lemma lem5946675 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946676 {A : Type'} (p : A -> A) (y : A) : (term439 A p y) = ((p y) = (p y)).
Proof. exact (@lem5946675 ((p y) = (p y))). Qed.
Lemma lem5946677 {A : Type'} (p : A -> A) (y : A) : (p y) = (p y).
Proof. exact (EQ_MP (@lem5946676 A p y) (@lem5946673 A p y)). Qed.
Lemma lem5946679 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A x s.
Proof. exact (proj1 (@lem5946180 A s x p y h1)). Qed.
Lemma lem5946680 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term355 A x s.
Proof. exact (fun h0 : term181 A x s => @lem5946679 A s x p y h1). Qed.
Lemma lem5946682 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946683 {A : Type'} (x : A) (s : A -> Prop) : (term355 A x s) = (@IN A x s).
Proof. exact (@lem5946682 (@IN A x s)). Qed.
Lemma lem5946684 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : @IN A x s.
Proof. exact (EQ_MP (@lem5946683 A x s) (@lem5946680 A s x p y h1)). Qed.
Lemma lem5946686 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : (p x) = (p y).
Proof. exact (proj2 (@lem5946280 A s x p y h1)). Qed.
Lemma lem5946687 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term441 A x p y.
Proof. exact (fun h0 : term442 A x p y => @lem5946686 A s x p y h1). Qed.
Lemma lem5946689 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5946690 {A : Type'} (x : A) (p : A -> A) (y : A) : (term441 A x p y) = ((p x) = (p y)).
Proof. exact (@lem5946689 ((p x) = (p y))). Qed.
Lemma lem5946691 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : (p x) = (p y).
Proof. exact (EQ_MP (@lem5946690 A x p y) (@lem5946687 A s x p y h1)). Qed.
Lemma lem5946707 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946708 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term437 A s p _75179 _75181 _75180) = (term443 A s p _75179 _75181 _75180).
Proof. exact (@lem5946707 (term435 A p _75180 _75179) (term181 A _75180 s) (term434 A s p _75179 _75181 _75180)). Qed.
Lemma lem5946734 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946735 {A : Type'} (p : A -> A) (_75179 : A) (s : A -> Prop) (_75181 : A) (_75180 : A) : (term434 A s p _75179 _75181 _75180) = (term444 A p _75179 s _75181 _75180).
Proof. exact (@lem5946734 (term435 A p _75181 _75179) (term181 A _75181 s) (_75181 = _75180)). Qed.
Lemma lem5946751 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5946752 {A : Type'} (_75180 : A) (_75181 : A) (s : A -> Prop) : (term445 A s _75181 _75180) = (term446 A _75180 _75181 s).
Proof. exact (@lem5946751 (_75181 = _75180) (term181 A _75181 s)). Qed.
Lemma lem5946760 {A : Type'} (p : A -> A) (_75181 : A) (_75179 : A) : (term447 A p _75181 _75179) = (term447 A p _75181 _75179).
Proof. exact (eq_refl (term447 A p _75181 _75179)). Qed.
Lemma lem5946761 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term444 A p _75179 s _75181 _75180) = (term448 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946760 A p _75181 _75179) (@lem5946752 A _75180 _75181 s)). Qed.
Lemma lem5946765 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946766 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term448 A p _75179 _75180 _75181 s) = (term449 A _75180 p _75179 _75181 s).
Proof. exact (@lem5946765 (_75181 = _75180) (term435 A p _75181 _75179) (term181 A _75181 s)). Qed.
Lemma lem5946786 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term444 A p _75179 s _75181 _75180) = (term449 A _75180 p _75179 _75181 s).
Proof. exact (TRANS (@lem5946761 A p _75179 _75180 _75181 s) (@lem5946766 A _75180 p _75179 _75181 s)). Qed.
Lemma lem5946787 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term434 A s p _75179 _75181 _75180) = (term449 A _75180 p _75179 _75181 s).
Proof. exact (TRANS (@lem5946735 A p _75179 s _75181 _75180) (@lem5946786 A _75180 p _75179 _75181 s)). Qed.
Lemma lem5946788 {A : Type'} (_75180 : A) (s : A -> Prop) : (term138 A _75180 s) = (term138 A _75180 s).
Proof. exact (eq_refl (term138 A _75180 s)). Qed.
Lemma lem5946789 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term450 A s p _75179 _75181 _75180) = (term451 A _75180 p _75179 _75181 s).
Proof. exact (MK_COMB (@lem5946788 A _75180 s) (@lem5946787 A _75180 p _75179 _75181 s)). Qed.
Lemma lem5946793 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946794 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term451 A _75180 p _75179 _75181 s) = (term452 A _75180 p _75179 _75181 s).
Proof. exact (@lem5946793 (_75181 = _75180) (term181 A _75180 s) (term453 A p _75179 _75181 s)). Qed.
Lemma lem5946810 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946811 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term454 A _75180 p _75179 _75181 s) = (term455 A p _75179 _75180 _75181 s).
Proof. exact (@lem5946810 (term435 A p _75181 _75179) (term181 A _75180 s) (term181 A _75181 s)). Qed.
Lemma lem5946829 {A : Type'} (_75181 : A) (_75180 : A) : (term456 A _75181 _75180) = (term456 A _75181 _75180).
Proof. exact (eq_refl (term456 A _75181 _75180)). Qed.
Lemma lem5946830 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term452 A _75180 p _75179 _75181 s) = (term457 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946829 A _75181 _75180) (@lem5946811 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946841 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term451 A _75180 p _75179 _75181 s) = (term457 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946794 A _75180 p _75179 _75181 s) (@lem5946830 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946842 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term450 A s p _75179 _75181 _75180) = (term457 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946789 A _75180 p _75179 _75181 s) (@lem5946841 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946843 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term447 A p _75180 _75179) = (term447 A p _75180 _75179).
Proof. exact (eq_refl (term447 A p _75180 _75179)). Qed.
Lemma lem5946844 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term443 A s p _75179 _75181 _75180) = (term458 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946843 A p _75180 _75179) (@lem5946842 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946848 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946849 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term458 A p _75179 _75180 _75181 s) = (term459 A p _75179 _75180 _75181 s).
Proof. exact (@lem5946848 (_75181 = _75180) (term435 A p _75180 _75179) (term455 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946891 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term443 A s p _75179 _75181 _75180) = (term459 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946844 A p _75179 _75180 _75181 s) (@lem5946849 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946892 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term437 A s p _75179 _75181 _75180) = (term459 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946708 A s p _75179 _75181 _75180) (@lem5946891 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946893 {A : Type'} (_75179 : A) (s : A -> Prop) : (term138 A _75179 s) = (term138 A _75179 s).
Proof. exact (eq_refl (term138 A _75179 s)). Qed.
Lemma lem5946894 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term438 A s p _75179 _75181 _75180) = (term460 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946893 A _75179 s) (@lem5946892 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946898 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946899 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term460 A p _75179 _75180 _75181 s) = (term461 A p _75179 _75180 _75181 s).
Proof. exact (@lem5946898 (_75181 = _75180) (term181 A _75179 s) (term462 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946915 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946916 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term463 A p _75179 _75180 _75181 s) = (term464 A p _75179 _75180 _75181 s).
Proof. exact (@lem5946915 (term435 A p _75180 _75179) (term181 A _75179 s) (term455 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946932 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5946933 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term465 A p _75179 _75180 _75181 s) = (term466 A p _75179 _75180 _75181 s).
Proof. exact (@lem5946932 (term435 A p _75181 _75179) (term181 A _75179 s) (term467 A _75180 _75181 s)). Qed.
Lemma lem5946961 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term447 A p _75180 _75179) = (term447 A p _75180 _75179).
Proof. exact (eq_refl (term447 A p _75180 _75179)). Qed.
Lemma lem5946962 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term464 A p _75179 _75180 _75181 s) = (term468 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946961 A p _75180 _75179) (@lem5946933 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946973 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term463 A p _75179 _75180 _75181 s) = (term468 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946916 A p _75179 _75180 _75181 s) (@lem5946962 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946974 {A : Type'} (_75181 : A) (_75180 : A) : (term456 A _75181 _75180) = (term456 A _75181 _75180).
Proof. exact (eq_refl (term456 A _75181 _75180)). Qed.
Lemma lem5946975 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term461 A p _75179 _75180 _75181 s) = (term469 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946974 A _75181 _75180) (@lem5946973 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946986 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term460 A p _75179 _75180 _75181 s) = (term469 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946899 A p _75179 _75180 _75181 s) (@lem5946975 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946987 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term438 A s p _75179 _75181 _75180) = (term469 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5946894 A p _75179 _75180 _75181 s) (@lem5946986 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5946988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5946989 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term470 A s p _75179 _75181 _75180) = (term471 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5946988) (@lem5946987 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947015 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5947016 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term472 A _75180 s p _75181 _75179) = (term473 A _75180 s p _75181 _75179).
Proof. exact (@lem5947015 (term435 A p _75180 _75179) (term181 A _75180 s) (term113 A s p _75181 _75179)). Qed.
Lemma lem5947042 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5947043 {A : Type'} (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term113 A s p _75181 _75179) = (term453 A p _75179 _75181 s).
Proof. exact (@lem5947042 (term435 A p _75181 _75179) (term181 A _75181 s)). Qed.
Lemma lem5947051 {A : Type'} (_75180 : A) (s : A -> Prop) : (term138 A _75180 s) = (term138 A _75180 s).
Proof. exact (eq_refl (term138 A _75180 s)). Qed.
Lemma lem5947052 {A : Type'} (_75180 : A) (p : A -> A) (_75179 : A) (_75181 : A) (s : A -> Prop) : (term474 A _75180 s p _75181 _75179) = (term454 A _75180 p _75179 _75181 s).
Proof. exact (MK_COMB (@lem5947051 A _75180 s) (@lem5947043 A p _75179 _75181 s)). Qed.
Lemma lem5947056 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5947057 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term454 A _75180 p _75179 _75181 s) = (term455 A p _75179 _75180 _75181 s).
Proof. exact (@lem5947056 (term435 A p _75181 _75179) (term181 A _75180 s) (term181 A _75181 s)). Qed.
Lemma lem5947075 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term474 A _75180 s p _75181 _75179) = (term455 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5947052 A _75180 p _75179 _75181 s) (@lem5947057 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947076 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term447 A p _75180 _75179) = (term447 A p _75180 _75179).
Proof. exact (eq_refl (term447 A p _75180 _75179)). Qed.
Lemma lem5947077 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term473 A _75180 s p _75181 _75179) = (term462 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5947076 A p _75180 _75179) (@lem5947075 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947088 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term472 A _75180 s p _75181 _75179) = (term462 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5947016 A _75180 s p _75181 _75179) (@lem5947077 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947089 {A : Type'} (_75179 : A) (s : A -> Prop) : (term138 A _75179 s) = (term138 A _75179 s).
Proof. exact (eq_refl (term138 A _75179 s)). Qed.
Lemma lem5947090 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term475 A _75180 s p _75181 _75179) = (term463 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5947089 A _75179 s) (@lem5947088 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947094 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5947095 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term463 A p _75179 _75180 _75181 s) = (term464 A p _75179 _75180 _75181 s).
Proof. exact (@lem5947094 (term435 A p _75180 _75179) (term181 A _75179 s) (term455 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947111 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5947112 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term465 A p _75179 _75180 _75181 s) = (term466 A p _75179 _75180 _75181 s).
Proof. exact (@lem5947111 (term435 A p _75181 _75179) (term181 A _75179 s) (term467 A _75180 _75181 s)). Qed.
Lemma lem5947140 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term447 A p _75180 _75179) = (term447 A p _75180 _75179).
Proof. exact (eq_refl (term447 A p _75180 _75179)). Qed.
Lemma lem5947141 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term464 A p _75179 _75180 _75181 s) = (term468 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5947140 A p _75180 _75179) (@lem5947112 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947152 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term463 A p _75179 _75180 _75181 s) = (term468 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5947095 A p _75179 _75180 _75181 s) (@lem5947141 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947153 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term475 A _75180 s p _75181 _75179) = (term468 A p _75179 _75180 _75181 s).
Proof. exact (TRANS (@lem5947090 A p _75179 _75180 _75181 s) (@lem5947152 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947154 {A : Type'} (_75181 : A) (_75180 : A) : (term456 A _75181 _75180) = (term456 A _75181 _75180).
Proof. exact (eq_refl (term456 A _75181 _75180)). Qed.
Lemma lem5947155 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : (term476 A _75180 s p _75181 _75179) = (term469 A p _75179 _75180 _75181 s).
Proof. exact (MK_COMB (@lem5947154 A _75181 _75180) (@lem5947153 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947166 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : ((term438 A s p _75179 _75181 _75180) = (term476 A _75180 s p _75181 _75179)) = ((term469 A p _75179 _75180 _75181 s) = (term469 A p _75179 _75180 _75181 s)).
Proof. exact (MK_COMB (@lem5946989 A p _75179 _75180 _75181 s) (@lem5947155 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947168 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5947169 (x : Prop) : (x = x) = True.
Proof. exact (@lem5947168 Prop x). Qed.
Lemma lem5947170 {A : Type'} (p : A -> A) (_75179 : A) (_75180 : A) (_75181 : A) (s : A -> Prop) : ((term469 A p _75179 _75180 _75181 s) = (term469 A p _75179 _75180 _75181 s)) = True.
Proof. exact (@lem5947169 (term469 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947171 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : ((term438 A s p _75179 _75181 _75180) = (term476 A _75180 s p _75181 _75179)) = True.
Proof. exact (TRANS (@lem5947166 A p _75179 _75180 _75181 s) (@lem5947170 A p _75179 _75180 _75181 s)). Qed.
Lemma lem5947172 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : True = ((term438 A s p _75179 _75181 _75180) = (term476 A _75180 s p _75181 _75179)).
Proof. exact (SYM (@lem5947171 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947173 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term438 A s p _75179 _75181 _75180) = (term476 A _75180 s p _75181 _75179).
Proof. exact (EQ_MP (@lem5947172 A _75180 s p _75181 _75179) (@lem0)). Qed.
Lemma lem5947174 {A : Type'} (_75180 : A) (_75181 : A) (_75179 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term476 A _75180 s p _75181 _75179.
Proof. exact (EQ_MP (@lem5947173 A _75180 s p _75181 _75179) (@lem5946550 A _75179 _75181 _75180 x' s p h1)). Qed.
Lemma lem5947176 (b : Prop) (a : Prop) : (a \/ b) = (term360 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5947177 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term476 A _75180 s p _75181 _75179) = (term477 A s p _75179 _75181 _75180).
Proof. exact (@lem5947176 (term475 A _75180 s p _75181 _75179) (_75181 = _75180)). Qed.
Lemma lem5947179 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5947180 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term478 A _75180 s p _75181 _75179) = (term479 A _75180 s p _75181 _75179).
Proof. exact (@lem5947179 (term181 A _75179 s) (term472 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947182 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5947183 {A : Type'} (_75179 : A) (s : A -> Prop) : (term362 A _75179 s) = (@IN A _75179 s).
Proof. exact (@lem5947182 (@IN A _75179 s)). Qed.
Lemma lem5947184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947185 {A : Type'} (_75179 : A) (s : A -> Prop) : (term480 A _75179 s) = (term232 A _75179 s).
Proof. exact (MK_COMB (@lem5947184) (@lem5947183 A _75179 s)). Qed.
Lemma lem5947187 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5947188 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term481 A _75180 s p _75181 _75179) = (term482 A _75180 s p _75181 _75179).
Proof. exact (@lem5947187 (term181 A _75180 s) (term483 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947190 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5947191 {A : Type'} (_75180 : A) (s : A -> Prop) : (term362 A _75180 s) = (@IN A _75180 s).
Proof. exact (@lem5947190 (@IN A _75180 s)). Qed.
Lemma lem5947192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947193 {A : Type'} (_75180 : A) (s : A -> Prop) : (term480 A _75180 s) = (term232 A _75180 s).
Proof. exact (MK_COMB (@lem5947192) (@lem5947191 A _75180 s)). Qed.
Lemma lem5947195 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5947196 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term484 A _75180 s p _75181 _75179) = (term485 A _75180 s p _75181 _75179).
Proof. exact (@lem5947195 (term435 A p _75180 _75179) (term113 A s p _75181 _75179)). Qed.
Lemma lem5947198 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5947199 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term486 A p _75180 _75179) = ((p _75180) = _75179).
Proof. exact (@lem5947198 ((p _75180) = _75179)). Qed.
Lemma lem5947200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947201 {A : Type'} (p : A -> A) (_75180 : A) (_75179 : A) : (term487 A p _75180 _75179) = (term488 A p _75180 _75179).
Proof. exact (MK_COMB (@lem5947200) (@lem5947199 A p _75180 _75179)). Qed.
Lemma lem5947203 (a : Prop) (b : Prop) : (term379 a b) = (term380 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5947204 {A : Type'} (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term489 A s p _75181 _75179) = (term490 A s p _75181 _75179).
Proof. exact (@lem5947203 (term181 A _75181 s) (term435 A p _75181 _75179)). Qed.
Lemma lem5947206 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5947207 {A : Type'} (_75181 : A) (s : A -> Prop) : (term362 A _75181 s) = (@IN A _75181 s).
Proof. exact (@lem5947206 (@IN A _75181 s)). Qed.
Lemma lem5947208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5947209 {A : Type'} (_75181 : A) (s : A -> Prop) : (term480 A _75181 s) = (term232 A _75181 s).
Proof. exact (MK_COMB (@lem5947208) (@lem5947207 A _75181 s)). Qed.
Lemma lem5947211 (a : Prop) : (term75 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5947212 {A : Type'} (p : A -> A) (_75181 : A) (_75179 : A) : (term486 A p _75181 _75179) = ((p _75181) = _75179).
Proof. exact (@lem5947211 ((p _75181) = _75179)). Qed.
Lemma lem5947213 {A : Type'} (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term490 A s p _75181 _75179) = (term98 A s p _75181 _75179).
Proof. exact (MK_COMB (@lem5947209 A _75181 s) (@lem5947212 A p _75181 _75179)). Qed.
Lemma lem5947214 {A : Type'} (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term489 A s p _75181 _75179) = (term98 A s p _75181 _75179).
Proof. exact (TRANS (@lem5947204 A s p _75181 _75179) (@lem5947213 A s p _75181 _75179)). Qed.
Lemma lem5947215 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term485 A _75180 s p _75181 _75179) = (term491 A _75180 s p _75181 _75179).
Proof. exact (MK_COMB (@lem5947201 A p _75180 _75179) (@lem5947214 A s p _75181 _75179)). Qed.
Lemma lem5947216 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term484 A _75180 s p _75181 _75179) = (term491 A _75180 s p _75181 _75179).
Proof. exact (TRANS (@lem5947196 A _75180 s p _75181 _75179) (@lem5947215 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947217 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term482 A _75180 s p _75181 _75179) = (term492 A _75180 s p _75181 _75179).
Proof. exact (MK_COMB (@lem5947193 A _75180 s) (@lem5947216 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947218 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term481 A _75180 s p _75181 _75179) = (term492 A _75180 s p _75181 _75179).
Proof. exact (TRANS (@lem5947188 A _75180 s p _75181 _75179) (@lem5947217 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947219 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term479 A _75180 s p _75181 _75179) = (term493 A _75180 s p _75181 _75179).
Proof. exact (MK_COMB (@lem5947185 A _75179 s) (@lem5947218 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947220 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term478 A _75180 s p _75181 _75179) = (term493 A _75180 s p _75181 _75179).
Proof. exact (TRANS (@lem5947180 A _75180 s p _75181 _75179) (@lem5947219 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5947222 {A : Type'} (_75180 : A) (s : A -> Prop) (p : A -> A) (_75181 : A) (_75179 : A) : (term494 A _75180 s p _75181 _75179) = (term495 A _75180 s p _75181 _75179).
Proof. exact (MK_COMB (@lem5947221) (@lem5947220 A _75180 s p _75181 _75179)). Qed.
Lemma lem5947223 {A : Type'} (_75181 : A) (_75180 : A) : (_75181 = _75180) = (_75181 = _75180).
Proof. exact (eq_refl (_75181 = _75180)). Qed.
Lemma lem5947224 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term477 A s p _75179 _75181 _75180) = (term496 A s p _75179 _75181 _75180).
Proof. exact (MK_COMB (@lem5947222 A _75180 s p _75181 _75179) (@lem5947223 A _75181 _75180)). Qed.
Lemma lem5947225 {A : Type'} (s : A -> Prop) (p : A -> A) (_75179 : A) (_75181 : A) (_75180 : A) : (term476 A _75180 s p _75181 _75179) = (term496 A s p _75179 _75181 _75180).
Proof. exact (TRANS (@lem5947177 A s p _75179 _75181 _75180) (@lem5947224 A s p _75179 _75181 _75180)). Qed.
Lemma lem5947227 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term497 A s x p y.
Proof. exact (conj (@lem5946684 A s x p y h1) (@lem5946691 A s x p y h1)). Qed.
Lemma lem5947228 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term498 A s x p y.
Proof. exact (conj (@lem5946677 A p y) (@lem5947227 A s x p y h1)). Qed.
Lemma lem5947229 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term432 A s x p y) : term499 A s x p y.
Proof. exact (conj (@lem5946668 A s x p y h1) (@lem5947228 A s x p y h1)). Qed.
Lemma lem5947230 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term432 A s x p y) : term500 A s x p y.
Proof. exact (conj (@lem5946661 A s x p y h1 h2) (@lem5947229 A s x p y h2)). Qed.
Lemma lem5947232 {A : Type'} (_75179 : A) (_75181 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term496 A s p _75179 _75181 _75180.
Proof. exact (EQ_MP (@lem5947225 A s p _75179 _75181 _75180) (@lem5947174 A _75180 _75181 _75179 x' s p h1)). Qed.
Lemma lem5947233 {A : Type'} (_75179 : A) (_75181 : A) (_75180 : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term496 A s p _75179 _75181 _75180.
Proof. exact (@lem5947232 A _75179 _75181 _75180 x' s p h1). Qed.
Lemma lem5947234 {A : Type'} (x : A) (y : A) (x' : A -> A) (s : A -> Prop) (p : A -> A) (h1 : term215 A x' s p) : term501 A s p x y.
Proof. exact (@lem5947233 A (p y) x y x' s p h1). Qed.
Lemma lem5947237 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term432 A s x p y) : x = y.
Proof. exact (@lem5947234 A x y x' s p h2 (@lem5947230 A s x p y h1 h3)). Qed.
Lemma lem5947238 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term432 A s x p y) : term502 A x y.
Proof. exact (fun h0 : term371 A x y => @lem5947237 A x' s x p y h1 h2 h3). Qed.
Lemma lem5947240 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5947241 {A : Type'} (x : A) (y : A) : (term502 A x y) = (x = y).
Proof. exact (@lem5947240 (x = y)). Qed.
Lemma lem5947242 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term432 A s x p y) : x = y.
Proof. exact (EQ_MP (@lem5947241 A x y) (@lem5947238 A x' s x p y h1 h2 h3)). Qed.
Lemma lem5947245 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5947247 {A : Type'} (x : A) (y : A) : (term371 A x y) = (term503 A x y).
Proof. exact (@lem5947245 (x = y)). Qed.
Lemma lem5947250 {A : Type'} (x : A) (y : A) (h1 : term371 A x y) : term503 A x y.
Proof. exact (EQ_MP (@lem5947247 A x y) (@lem5946518 A x y h1)). Qed.
Lemma lem5947253 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (@lem5947250 A x y h3 (@lem5947242 A x' s x p y h1 h2 h4)). Qed.
Lemma lem5947254 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : term404.
Proof. exact (fun h0 : ~ False => @lem5947253 A x' s x p y h1 h2 h3 h4). Qed.
Lemma lem5947256 (p : Prop) : (term356 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5947257 : term404 = False.
Proof. exact (@lem5947256 False). Qed.
Lemma lem5947258 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947257) (@lem5947254 A x' s x p y h1 h2 h3 h4)). Qed.
Lemma lem5947259 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947258 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946518 A x y h3)). Qed.
Lemma lem5947260 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947259 A x' s x p y h1 h2 h3 h4) (@lem5946518 A x y h3)). Qed.
Lemma lem5947261 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947260 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946300 A x y h3)). Qed.
Lemma lem5947262 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947261 A x' s x p y h1 h2 h3 h4) (@lem5946300 A x y h3)). Qed.
Lemma lem5947263 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947262 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946300 A x y h3)). Qed.
Lemma lem5947264 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947263 A x' s x p y h1 h2 h3 h4) (@lem5946300 A x y h3)). Qed.
Lemma lem5947265 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term215 A x' s p) = False.
Proof. exact (prop_ext (fun h5 : term215 A x' s p => @lem5947264 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946279 A x' s p h2)). Qed.
Lemma lem5947266 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947265 A x' s x p y h1 h2 h3 h4) (@lem5946279 A x' s p h2)). Qed.
Lemma lem5947267 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947266 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946188 A x y h3)). Qed.
Lemma lem5947268 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947267 A x' s x p y h1 h2 h3 h4) (@lem5946188 A x y h3)). Qed.
Lemma lem5947269 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term432 A s x p y) = False.
Proof. exact (prop_ext (fun h5 : term432 A s x p y => @lem5947268 A x' s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946180 A s x p y h4)). Qed.
Lemma lem5947270 {A : Type'} (x' : A -> A) (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term40 A p s) (h2 : term215 A x' s p) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947269 A x' s x p y h1 h2 h3 h4) (@lem5946180 A s x p y h4)). Qed.
Lemma lem5947271 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (ex_elim (@lem5946112 A s p h1) (fun x' : A -> A => fun h0 : term217 A s p x' => @lem5947270 A x' s x p y h2 h0 h3 h4)). Qed.
Lemma lem5947272 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947271 A s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946132 A x y h3)). Qed.
Lemma lem5947273 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947272 A s x p y h1 h2 h3 h4) (@lem5946132 A x y h3)). Qed.
Lemma lem5947274 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term432 A s x p y) = False.
Proof. exact (prop_ext (fun h5 : term432 A s x p y => @lem5947273 A s x p y h1 h2 h3 h4) (fun h5 : False => @lem5946126 A s x p y h4)). Qed.
Lemma lem5947275 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947274 A s x p y h1 h2 h3 h4) (@lem5946126 A s x p y h4)). Qed.
Lemma lem5947276 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : (term371 A x y) = False.
Proof. exact (prop_ext (fun h5 : term371 A x y => @lem5947275 A s x p y h1 h2 h3 h4) (fun h5 : False => @lem5945637 A x y h3)). Qed.
Lemma lem5947277 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term371 A x y) (h4 : term432 A s x p y) : False.
Proof. exact (EQ_MP (@lem5947276 A s x p y h1 h2 h3 h4) (@lem5945637 A x y h3)). Qed.
Lemma lem5947278 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term432 A s x p y) : term431 A x y.
Proof. exact (fun h0 : term371 A x y => @lem5947277 A s x p y h1 h2 h0 h3). Qed.
Lemma lem5947279 {A : Type'} (s : A -> Prop) (x : A) (p : A -> A) (y : A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term432 A s x p y) : x = y.
Proof. exact (EQ_MP (@lem5945636 A x y) (@lem5947278 A s x p y h1 h2 h3)). Qed.
Lemma lem5947280 {A : Type'} (x : A) (y : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term427 A s p x y.
Proof. exact (fun h0 : term432 A s x p y => @lem5947279 A s x p y h1 h2 h0). Qed.
Lemma lem5947285 {A : Type'} (x : A) (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term429 A s p x.
Proof. exact (fun y : A => @lem5947280 A x y p s h1 h2). Qed.
Lemma lem5947290 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term57 A s p.
Proof. exact (fun x : A => @lem5947285 A x p s h1 h2). Qed.
Lemma lem5947291 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term417 A s p.
Proof. exact (fun h0 : term39 A s p => @lem5947290 A p s h0 h1). Qed.
Lemma lem5947292 {A : Type'} (s : A -> Prop) (p : A -> A) : term418 A s p.
Proof. exact (fun h0 : term40 A p s => @lem5947291 A p s h0). Qed.
Lemma lem5947297 {A : Type'} (p : A -> A) : term422 A p.
Proof. exact (fun s : A -> Prop => @lem5947292 A s p). Qed.
Lemma lem5947302 {A : Type'} : term426 A.
Proof. exact (fun p : A -> A => @lem5947297 A p). Qed.
Lemma lem5947303 {A : Type'} : term425 A.
Proof. exact (EQ_MP (@lem5945629 A) (@lem5947302 A)). Qed.
Lemma lem5947304 {A : Type'} (p : A -> A) : term504 A p.
Proof. exact (@lem5947303 A p). Qed.
Lemma lem5947305 {A : Type'} (p : A -> A) : (term504 A p) = (term421 A p).
Proof. exact (eq_refl (term504 A p)). Qed.
Lemma lem5947306 {A : Type'} (p : A -> A) : term421 A p.
Proof. exact (EQ_MP (@lem5947305 A p) (@lem5947304 A p)). Qed.
Lemma lem5947307 {A : Type'} (p : A -> A) (s : A -> Prop) : term505 A p s.
Proof. exact (@lem5947306 A p s). Qed.
Lemma lem5947308 {A : Type'} (s : A -> Prop) (p : A -> A) : (term505 A p s) = (term411 A s p).
Proof. exact (eq_refl (term505 A p s)). Qed.
Lemma lem5947309 {A : Type'} (s : A -> Prop) (p : A -> A) : term411 A s p.
Proof. exact (EQ_MP (@lem5947308 A s p) (@lem5947307 A p s)). Qed.
Lemma lem5947311 {A : Type'} (s : A -> Prop) (p : A -> A) : term411 A s p.
Proof. exact (@lem5945446 A s p (@lem5947309 A s p)). Qed.
Lemma lem5947312 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term40 A p s) : term416 A s p.
Proof. exact (@lem5947311 A s p (@lem5943016 A p s h1)). Qed.
Lemma lem5947313 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term409 A s p.
Proof. exact (@lem5947312 A p s h2 (@lem5943015 A s p h1)). Qed.
Lemma lem5947314 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term410 A s p) : False.
Proof. exact (@lem5947313 A p s h1 h2 (@lem5945430 A s p h3)). Qed.
Lemma lem5947315 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term410 A s p) : (term410 A s p) = False.
Proof. exact (prop_ext (fun h4 : term410 A s p => @lem5947314 A s p h1 h2 h3) (fun h4 : False => @lem5945430 A s p h3)). Qed.
Lemma lem5947316 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : term410 A s p) : False.
Proof. exact (EQ_MP (@lem5947315 A s p h1 h2 h3) (@lem5945430 A s p h3)). Qed.
Lemma lem5947317 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term409 A s p.
Proof. exact (fun h0 : term410 A s p => @lem5947316 A s p h1 h2 h0). Qed.
Lemma lem5947318 {A : Type'} (p : A -> A) (s : A -> Prop) (h1 : term39 A s p) (h2 : term40 A p s) : term57 A s p.
Proof. exact (EQ_MP (@lem5945429 A s p) (@lem5947317 A p s h1 h2)). Qed.
Lemma lem5947319 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (term58 A B op p s f) = (term42 A B op s f p).
Proof. exact (@lem5943107 A B s f p op h3 (@lem5947318 A p s h1 h2)). Qed.
Lemma lem5947320 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : s = (@IMAGE A A p s).
Proof. exact (EQ_MP (@lem5943065 A p s) (@lem5945425 A B p s op h1 h2 h3)). Qed.
Lemma lem5947321 {A B : Type'} (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (@iterate B A op s) = (term506 A B op p s).
Proof. exact (MK_COMB (@lem5943022 A B op) (@lem5947320 A B p s op h1 h2 h3)). Qed.
Lemma lem5947322 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (@iterate B A op s f) = (term58 A B op p s f).
Proof. exact (MK_COMB (@lem5947321 A B p s op h1 h2 h3) (@lem5943021 A B f)). Qed.
Lemma lem5947323 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : term507 A B op s f p.
Proof. exact (conj (@lem5947322 A B f p s op h1 h2 h3) (@lem5947319 A B f p s op h1 h2 h3)). Qed.
Lemma lem5947324 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : term508 A B op s f p.
Proof. exact (ex_intro (term509 A B op s f p) (term58 A B op p s f) (@lem5947323 A B f p s op h1 h2 h3)). Qed.
Lemma lem5947325 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (@iterate B A op s f) = (term42 A B op s f p).
Proof. exact (@lem5943020 A B op s f p (@lem5947324 A B f p s op h1 h2 h3)). Qed.
Lemma lem5947326 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term38 A s p) : term39 A s p.
Proof. exact (proj2 (@lem5943014 A s p h1)). Qed.
Lemma lem5947327 {A : Type'} (s : A -> Prop) (p : A -> A) (h1 : term38 A s p) : term40 A p s.
Proof. exact (proj1 (@lem5943014 A s p h1)). Qed.
Lemma lem5947328 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (term39 A s p) = ((@iterate B A op s f) = (term42 A B op s f p)).
Proof. exact (prop_ext (fun h4 : term39 A s p => @lem5947325 A B f p s op h1 h2 h3) (fun h4 : (@iterate B A op s f) = (term42 A B op s f p) => @lem5943015 A s p h1)). Qed.
Lemma lem5947329 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (@iterate B A op s f) = (term42 A B op s f p).
Proof. exact (EQ_MP (@lem5947328 A B f p s op h1 h2 h3) (@lem5943015 A s p h1)). Qed.
Lemma lem5947330 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (term40 A p s) = ((@iterate B A op s f) = (term42 A B op s f p)).
Proof. exact (prop_ext (fun h4 : term40 A p s => @lem5947329 A B f p s op h1 h2 h3) (fun h4 : (@iterate B A op s f) = (term42 A B op s f p) => @lem5943016 A p s h2)). Qed.
Lemma lem5947331 {A B : Type'} (f : A -> B) (p : A -> A) (s : A -> Prop) (op : type1400 B) (h1 : term39 A s p) (h2 : term40 A p s) (h3 : @monoidal B op) : (@iterate B A op s f) = (term42 A B op s f p).
Proof. exact (EQ_MP (@lem5947330 A B f p s op h1 h2 h3) (@lem5943016 A p s h2)). Qed.
Lemma lem5947332 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term40 A p s) (h2 : @monoidal B op) (h3 : term38 A s p) : (term39 A s p) = ((@iterate B A op s f) = (term42 A B op s f p)).
Proof. exact (prop_ext (fun h4 : term39 A s p => @lem5947331 A B f p s op h4 h1 h2) (fun h4 : (@iterate B A op s f) = (term42 A B op s f p) => @lem5947326 A s p h3)). Qed.
Lemma lem5947333 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : term40 A p s) (h2 : @monoidal B op) (h3 : term38 A s p) : (@iterate B A op s f) = (term42 A B op s f p).
Proof. exact (EQ_MP (@lem5947332 A B f op s p h1 h2 h3) (@lem5947326 A s p h3)). Qed.
Lemma lem5947334 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @monoidal B op) (h2 : term38 A s p) : (term40 A p s) = ((@iterate B A op s f) = (term42 A B op s f p)).
Proof. exact (prop_ext (fun h3 : term40 A p s => @lem5947333 A B f op s p h3 h1 h2) (fun h3 : (@iterate B A op s f) = (term42 A B op s f p) => @lem5947327 A s p h2)). Qed.
Lemma lem5947335 {A B : Type'} (f : A -> B) (op : type1400 B) (s : A -> Prop) (p : A -> A) (h1 : @monoidal B op) (h2 : term38 A s p) : (@iterate B A op s f) = (term42 A B op s f p).
Proof. exact (EQ_MP (@lem5947334 A B f op s p h1 h2) (@lem5947327 A s p h2)). Qed.
Lemma lem5947336 {A B : Type'} (s : A -> Prop) (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term510 A B op s f p.
Proof. exact (fun h0 : term38 A s p => @lem5947335 A B f op s p h1 h0). Qed.
Lemma lem5947341 {A B : Type'} (f : A -> B) (p : A -> A) (op : type1400 B) (h1 : @monoidal B op) : term511 A B op f p.
Proof. exact (fun s : A -> Prop => @lem5947336 A B s f p op h1). Qed.
Lemma lem5947346 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term512 A B op f.
Proof. exact (fun p : A -> A => @lem5947341 A B f p op h1). Qed.
Lemma lem5947351 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term513 A B op.
Proof. exact (fun f : A -> B => @lem5947346 A B f op h1). Qed.
Lemma lem5947352 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term513 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem5947351 A B op h1) (fun h2 : term513 A B op => @lem5943013 B op h1)). Qed.
Lemma lem5947353 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term513 A B op.
Proof. exact (EQ_MP (@lem5947352 A B op h1) (@lem5943013 B op h1)). Qed.
Lemma lem5947354 {A B : Type'} (op : type1400 B) : term514 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5947353 A B op h0). Qed.
Lemma lem5947359 {A B : Type'} : term515 A B.
Proof. exact (fun op : type1400 B => @lem5947354 A B op). Qed.
