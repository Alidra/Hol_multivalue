Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_IDEMPOT_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import ARBITRARY_UNION_OF_INC_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_IN_GSPEC_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import FORALL_IN_IMAGE_spec.
Require Import FUN_EQ_THM_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import RIGHT_IMP_EXISTS_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import UNIONS_IMAGE_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm7_spec.
Lemma lem4860963 {_89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 : Type'} (Q : _89357 -> Prop) : term0 _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q.
Proof. exact (proj2 (@lem3449335 Prop _89212 _89213 _89280 _89281 _89282 _89357 _89358 _89359 _89360 _89361 Q)). Qed.
Lemma lem4860979 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) : term1 _89212 _89213 _89357 Q.
Proof. exact (proj1 (@lem4860963 _89212 _89213 Prop Prop Prop _89357 Prop Prop Prop Prop Q)). Qed.
Lemma lem4860980 {_89212 _89213 _89357 : Type'} (Q : _89357 -> Prop) (P : type1470 _89212 _89213) : term2 _89212 _89213 _89357 Q P.
Proof. exact (@lem4860979 _89212 _89213 _89357 Q P). Qed.
Lemma lem4860981 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : (term2 _89212 _89213 _89357 Q P) = (term3 _89212 _89213 _89357 P Q).
Proof. exact (eq_refl (term2 _89212 _89213 _89357 Q P)). Qed.
Lemma lem4860982 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) : term3 _89212 _89213 _89357 P Q.
Proof. exact (EQ_MP (@lem4860981 _89212 _89213 _89357 P Q) (@lem4860980 _89212 _89213 _89357 Q P)). Qed.
Lemma lem4860983 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : term4 _89212 _89213 _89357 P Q f.
Proof. exact (@lem4860982 _89212 _89213 _89357 P Q f). Qed.
Lemma lem4860984 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term4 _89212 _89213 _89357 P Q f) = ((term5 _89212 _89213 _89357 P f Q) = (term6 _89212 _89213 _89357 P Q f)).
Proof. exact (eq_refl (term4 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem4860993 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term7 _89422 _89438 f.
Proof. exact (@lem3452302 _89422 _89438 f). Qed.
Lemma lem4860994 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : (term7 _89422 _89438 f) = (term8 _89422 _89438 f).
Proof. exact (eq_refl (term7 _89422 _89438 f)). Qed.
Lemma lem4860995 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) : term8 _89422 _89438 f.
Proof. exact (EQ_MP (@lem4860994 _89422 _89438 f) (@lem4860993 _89422 _89438 f)). Qed.
Lemma lem4860996 {_89422 _89438 : Type'} (f : type1470 _89422 _89438) (s : _89438 -> Prop) : term9 _89422 _89438 f s.
Proof. exact (@lem4860995 _89422 _89438 f s). Qed.
Lemma lem4860997 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term9 _89422 _89438 f s) = ((term10 _89422 _89438 f s) = (term11 _89422 _89438 s f)).
Proof. exact (eq_refl (term9 _89422 _89438 f s)). Qed.
Lemma lem4860999 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term12 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem4861015 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term13 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem4860999 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4861016 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term14 _88961 _88962 _89106 Q P.
Proof. exact (@lem4861015 _88961 _88962 _89106 Q P). Qed.
Lemma lem4861017 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term14 _88961 _88962 _89106 Q P) = (term15 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term14 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4861018 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term15 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem4861017 _88961 _88962 _89106 P Q) (@lem4861016 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4861019 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term16 _88961 _88962 _89106 P Q f.
Proof. exact (@lem4861018 _88961 _88962 _89106 P Q f). Qed.
Lemma lem4861020 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term16 _88961 _88962 _89106 P Q f) = ((term17 _88961 _88962 _89106 P f Q) = (term18 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term16 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4861029 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term19 _87967 _87968 P f.
Proof. exact (@lem3386920 _87967 _87968 P f). Qed.
Lemma lem4861030 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : (term19 _87967 _87968 P f) = (term20 _87967 _87968 P f).
Proof. exact (eq_refl (term19 _87967 _87968 P f)). Qed.
Lemma lem4861031 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) : term20 _87967 _87968 P f.
Proof. exact (EQ_MP (@lem4861030 _87967 _87968 P f) (@lem4861029 _87967 _87968 P f)). Qed.
Lemma lem4861032 {_87967 _87968 : Type'} (P : _87967 -> Prop) (f : _87968 -> _87967) (s : _87968 -> Prop) : term21 _87967 _87968 P f s.
Proof. exact (@lem4861031 _87967 _87968 P f s). Qed.
Lemma lem4861033 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term21 _87967 _87968 P f s) = ((term22 _87967 _87968 f s P) = (term23 _87967 _87968 s P f)).
Proof. exact (eq_refl (term21 _87967 _87968 P f s)). Qed.
Lemma lem4861035 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4861036 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem4861037 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem4861036 A P) (@lem4861035 A P)). Qed.
Lemma lem4861038 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem4861037 A P Q). Qed.
Lemma lem4861039 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem4861041 {A B : Type'} (P : type1413 A B) : term29 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem4861042 {A B : Type'} (P : type1413 A B) : (term29 A B P) = ((term30 A B P) = (term31 A B P)).
Proof. exact (eq_refl (term29 A B P)). Qed.
Lemma lem4861044 {A : Type'} (P : Prop) : term32 A P.
Proof. exact (@lem12262 A P). Qed.
Lemma lem4861045 {A : Type'} (P : Prop) : (term32 A P) = (term33 A P).
Proof. exact (eq_refl (term32 A P)). Qed.
Lemma lem4861046 {A : Type'} (P : Prop) : term33 A P.
Proof. exact (EQ_MP (@lem4861045 A P) (@lem4861044 A P)). Qed.
Lemma lem4861047 {A : Type'} (P : Prop) (Q : A -> Prop) : term34 A P Q.
Proof. exact (@lem4861046 A P Q). Qed.
Lemma lem4861048 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = ((term35 A P Q) = (term36 A P Q)).
Proof. exact (eq_refl (term34 A P Q)). Qed.
Lemma lem4861050 {A : Type'} (P : A -> Prop) : term24 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem4861051 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (eq_refl (term24 A P)). Qed.
Lemma lem4861052 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (EQ_MP (@lem4861051 A P) (@lem4861050 A P)). Qed.
Lemma lem4861053 {A : Type'} (P : A -> Prop) (Q : Prop) : term26 A P Q.
Proof. exact (@lem4861052 A P Q). Qed.
Lemma lem4861054 {A : Type'} (P : A -> Prop) (Q : Prop) : (term26 A P Q) = ((term27 A P Q) = (term28 A P Q)).
Proof. exact (eq_refl (term26 A P Q)). Qed.
Lemma lem4861056 {A : Type'} (P : type180 A) : term37 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4861057 {A : Type'} (P : type180 A) : (term37 A P) = (term38 A P).
Proof. exact (eq_refl (term37 A P)). Qed.
Lemma lem4861058 {A : Type'} (P : type180 A) : term38 A P.
Proof. exact (EQ_MP (@lem4861057 A P) (@lem4861056 A P)). Qed.
Lemma lem4861059 {A : Type'} (P : type180 A) (Q : type686 A) : term39 A P Q.
Proof. exact (@lem4861058 A P Q). Qed.
Lemma lem4861060 {A : Type'} (P : type180 A) (Q : type686 A) : (term39 A P Q) = ((@UNION_OF A P Q) = (term40 A P Q)).
Proof. exact (eq_refl (term39 A P Q)). Qed.
Lemma lem4861062 {A : Type'} (P : type686 A) : term41 A P.
Proof. exact (@lem4858424 A P). Qed.
Lemma lem4861063 {A : Type'} (P : type686 A) : (term41 A P) = (term42 A P).
Proof. exact (eq_refl (term41 A P)). Qed.
Lemma lem4861064 {A : Type'} (P : type686 A) : term42 A P.
Proof. exact (EQ_MP (@lem4861063 A P) (@lem4861062 A P)). Qed.
Lemma lem4861065 {A : Type'} (P : type686 A) (s : A -> Prop) : term43 A P s.
Proof. exact (@lem4861064 A P s). Qed.
Lemma lem4861066 {A : Type'} (P : type686 A) (s : A -> Prop) : (term43 A P s) = (term44 A P s).
Proof. exact (eq_refl (term43 A P s)). Qed.
Lemma lem4861067 {A : Type'} (P : type686 A) (s : A -> Prop) : term44 A P s.
Proof. exact (EQ_MP (@lem4861066 A P s) (@lem4861065 A P s)). Qed.
Lemma lem4861068 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = ((term44 A P s) = True).
Proof. exact (@lem7 (term44 A P s)). Qed.
Lemma lem4861070 {A B : Type'} (f : A -> B) : term45 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4861071 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (eq_refl (term45 A B f)). Qed.
Lemma lem4861072 {A B : Type'} (f : A -> B) : term46 A B f.
Proof. exact (EQ_MP (@lem4861071 A B f) (@lem4861070 A B f)). Qed.
Lemma lem4861073 {A B : Type'} (f : A -> B) (g : A -> B) : term47 A B f g.
Proof. exact (@lem4861072 A B f g). Qed.
Lemma lem4861074 {A B : Type'} (f : A -> B) (g : A -> B) : (term47 A B f g) = ((f = g) = (term48 A B f g)).
Proof. exact (eq_refl (term47 A B f g)). Qed.
Lemma lem4861079 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term48 A B f g).
Proof. exact (EQ_MP (@lem4861074 A B f g) (@lem4861073 A B f g)). Qed.
Lemma lem4861080 {A : Type'} (f : type686 A) (g : type686 A) : (f = g) = (term49 A f g).
Proof. exact (@lem4861079 (A -> Prop) Prop f g). Qed.
Lemma lem4861081 {A : Type'} (P : type686 A) : ((term50 A P) = (@UNION_OF A (@ARBITRARY A) P)) = (term51 A P).
Proof. exact (@lem4861080 A (term50 A P) (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4861090 {A : Type'} (P : type686 A) : (term51 A P) = ((term50 A P) = (@UNION_OF A (@ARBITRARY A) P)).
Proof. exact (SYM (@lem4861081 A P)). Qed.
Lemma lem4861100 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = True.
Proof. exact (EQ_MP (@lem4861068 A P s) (@lem4861067 A P s)). Qed.
Lemma lem4861101 {A : Type'} (P : type686 A) (s : A -> Prop) : (term44 A P s) = True.
Proof. exact (@lem4861100 A P s). Qed.
Lemma lem4861102 {A : Type'} (P : type686 A) (s : A -> Prop) : (term52 A P s) = True.
Proof. exact (@lem4861101 A (@UNION_OF A (@ARBITRARY A) P) s). Qed.
Lemma lem4861103 {A : Type'} (P : type686 A) (s : A -> Prop) : True = (term52 A P s).
Proof. exact (SYM (@lem4861102 A P s)). Qed.
Lemma lem4861104 {A : Type'} (P : type686 A) (s : A -> Prop) : term52 A P s.
Proof. exact (EQ_MP (@lem4861103 A P s) (@lem0)). Qed.
Lemma lem4861108 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4861060 A P Q) (@lem4861059 A P Q)). Qed.
Lemma lem4861109 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4861108 A P Q). Qed.
Lemma lem4861110 {A : Type'} (P : type686 A) : (term50 A P) = (term53 A P).
Proof. exact (@lem4861109 A (@ARBITRARY A) (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4861126 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4861060 A P Q) (@lem4861059 A P Q)). Qed.
Lemma lem4861127 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4861126 A P Q). Qed.
Lemma lem4861128 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term54 A P).
Proof. exact (@lem4861127 A (@ARBITRARY A) P). Qed.
Lemma lem4861145 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4861146 {A : Type'} (P : type686 A) (c : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P c) = (term55 A P c).
Proof. exact (MK_COMB (@lem4861128 A P) (@lem4861145 A c)). Qed.
Lemma lem4861148 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4861149 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4861148 (A -> Prop) Prop f y). Qed.
Lemma lem4861150 {A : Type'} (P : type686 A) (c : A -> Prop) : (term58 A P c) = (term55 A P c).
Proof. exact (@lem4861149 A (term54 A P) c). Qed.
Lemma lem4861151 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4861152 {A : Type'} (P : type686 A) : (term60 A P) = (term54 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861151 A P s)). Qed.
Lemma lem4861153 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4861154 {A : Type'} (P : type686 A) (c : A -> Prop) : (term58 A P c) = (term55 A P c).
Proof. exact (MK_COMB (@lem4861152 A P) (@lem4861153 A c)). Qed.
Lemma lem4861155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861156 {A : Type'} (P : type686 A) (c : A -> Prop) : (term61 A P c) = (term62 A P c).
Proof. exact (MK_COMB (@lem4861155) (@lem4861154 A P c)). Qed.
Lemma lem4861157 {A : Type'} (P : type686 A) (c : A -> Prop) : (term55 A P c) = (term59 A P c).
Proof. exact (eq_refl (term55 A P c)). Qed.
Lemma lem4861158 {A : Type'} (P : type686 A) (c : A -> Prop) : ((term58 A P c) = (term55 A P c)) = ((term55 A P c) = (term59 A P c)).
Proof. exact (MK_COMB (@lem4861156 A P c) (@lem4861157 A P c)). Qed.
Lemma lem4861159 {A : Type'} (P : type686 A) (c : A -> Prop) : (term55 A P c) = (term59 A P c).
Proof. exact (EQ_MP (@lem4861158 A P c) (@lem4861150 A P c)). Qed.
Lemma lem4861176 {A : Type'} (P : type686 A) (c : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P c) = (term59 A P c).
Proof. exact (TRANS (@lem4861146 A P c) (@lem4861159 A P c)). Qed.
Lemma lem4861177 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4861178 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term64 A u P c) = (term65 A u P c).
Proof. exact (MK_COMB (@lem4861177 A c u) (@lem4861176 A P c)). Qed.
Lemma lem4861181 {A : Type'} (u : type686 A) (P : type686 A) : (term66 A u P) = (term67 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4861178 A u P c)). Qed.
Lemma lem4861182 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861183 {A : Type'} (u : type686 A) (P : type686 A) : (term68 A u P) = (term69 A u P).
Proof. exact (MK_COMB (@lem4861182 A) (@lem4861181 A u P)). Qed.
Lemma lem4861188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4861189 {A : Type'} (u : type686 A) (P : type686 A) : (term70 A u P) = (term71 A u P).
Proof. exact (MK_COMB (@lem4861188) (@lem4861183 A u P)). Qed.
Lemma lem4861192 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4861193 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term72 A P u s) = (term73 A P u s).
Proof. exact (MK_COMB (@lem4861189 A u P) (@lem4861192 A u s)). Qed.
Lemma lem4861196 {A : Type'} (u : type686 A) : (term74 A u) = (term74 A u).
Proof. exact (eq_refl (term74 A u)). Qed.
Lemma lem4861197 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term75 A P u s) = (term76 A P u s).
Proof. exact (MK_COMB (@lem4861196 A u) (@lem4861193 A P u s)). Qed.
Lemma lem4861200 {A : Type'} (P : type686 A) (s : A -> Prop) : (term77 A P s) = (term78 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4861197 A P u s)). Qed.
Lemma lem4861201 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4861202 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term80 A P s).
Proof. exact (MK_COMB (@lem4861201 A) (@lem4861200 A P s)). Qed.
Lemma lem4861207 {A : Type'} (P : type686 A) : (term53 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861202 A P s)). Qed.
Lemma lem4861208 {A : Type'} (P : type686 A) : (term50 A P) = (term81 A P).
Proof. exact (TRANS (@lem4861110 A P) (@lem4861207 A P)). Qed.
Lemma lem4861209 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4861210 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (term83 A P s).
Proof. exact (MK_COMB (@lem4861208 A P) (@lem4861209 A s)). Qed.
Lemma lem4861212 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4861213 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4861212 (A -> Prop) Prop f y). Qed.
Lemma lem4861214 {A : Type'} (P : type686 A) (s : A -> Prop) : (term84 A P s) = (term83 A P s).
Proof. exact (@lem4861213 A (term81 A P) s). Qed.
Lemma lem4861215 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (eq_refl (term83 A P s)). Qed.
Lemma lem4861216 {A : Type'} (P : type686 A) : (term85 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861215 A P s)). Qed.
Lemma lem4861217 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4861218 {A : Type'} (P : type686 A) (s : A -> Prop) : (term84 A P s) = (term83 A P s).
Proof. exact (MK_COMB (@lem4861216 A P) (@lem4861217 A s)). Qed.
Lemma lem4861219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861220 {A : Type'} (P : type686 A) (s : A -> Prop) : (term86 A P s) = (term87 A P s).
Proof. exact (MK_COMB (@lem4861219) (@lem4861218 A P s)). Qed.
Lemma lem4861221 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (eq_refl (term83 A P s)). Qed.
Lemma lem4861222 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term84 A P s) = (term83 A P s)) = ((term83 A P s) = (term80 A P s)).
Proof. exact (MK_COMB (@lem4861220 A P s) (@lem4861221 A P s)). Qed.
Lemma lem4861223 {A : Type'} (P : type686 A) (s : A -> Prop) : (term83 A P s) = (term80 A P s).
Proof. exact (EQ_MP (@lem4861222 A P s) (@lem4861214 A P s)). Qed.
Lemma lem4861256 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (term80 A P s).
Proof. exact (TRANS (@lem4861210 A P s) (@lem4861223 A P s)). Qed.
Lemma lem4861257 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861258 {A : Type'} (P : type686 A) (s : A -> Prop) : (term88 A P s) = (term89 A P s).
Proof. exact (MK_COMB (@lem4861257) (@lem4861256 A P s)). Qed.
Lemma lem4861260 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (EQ_MP (@lem4861060 A P Q) (@lem4861059 A P Q)). Qed.
Lemma lem4861261 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term40 A P Q).
Proof. exact (@lem4861260 A P Q). Qed.
Lemma lem4861262 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term54 A P).
Proof. exact (@lem4861261 A (@ARBITRARY A) P). Qed.
Lemma lem4861279 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4861280 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term55 A P s).
Proof. exact (MK_COMB (@lem4861262 A P) (@lem4861279 A s)). Qed.
Lemma lem4861282 {A B : Type'} (f : A -> B) (y : A) : (term56 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4861283 {A : Type'} (f : type686 A) (y : A -> Prop) : (term57 A f y) = (f y).
Proof. exact (@lem4861282 (A -> Prop) Prop f y). Qed.
Lemma lem4861284 {A : Type'} (P : type686 A) (s : A -> Prop) : (term58 A P s) = (term55 A P s).
Proof. exact (@lem4861283 A (term54 A P) s). Qed.
Lemma lem4861285 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4861286 {A : Type'} (P : type686 A) : (term60 A P) = (term54 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861285 A P s)). Qed.
Lemma lem4861287 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4861288 {A : Type'} (P : type686 A) (s : A -> Prop) : (term58 A P s) = (term55 A P s).
Proof. exact (MK_COMB (@lem4861286 A P) (@lem4861287 A s)). Qed.
Lemma lem4861289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861290 {A : Type'} (P : type686 A) (s : A -> Prop) : (term61 A P s) = (term62 A P s).
Proof. exact (MK_COMB (@lem4861289) (@lem4861288 A P s)). Qed.
Lemma lem4861291 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (eq_refl (term55 A P s)). Qed.
Lemma lem4861292 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term58 A P s) = (term55 A P s)) = ((term55 A P s) = (term59 A P s)).
Proof. exact (MK_COMB (@lem4861290 A P s) (@lem4861291 A P s)). Qed.
Lemma lem4861293 {A : Type'} (P : type686 A) (s : A -> Prop) : (term55 A P s) = (term59 A P s).
Proof. exact (EQ_MP (@lem4861292 A P s) (@lem4861284 A P s)). Qed.
Lemma lem4861310 {A : Type'} (P : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) P s) = (term59 A P s).
Proof. exact (TRANS (@lem4861280 A P s) (@lem4861293 A P s)). Qed.
Lemma lem4861311 {A : Type'} (P : type686 A) (s : A -> Prop) : (term90 A P s) = (term91 A P s).
Proof. exact (MK_COMB (@lem4861258 A P s) (@lem4861310 A P s)). Qed.
Lemma lem4861313 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem4861054 A P Q) (@lem4861053 A P Q)). Qed.
Lemma lem4861314 {A : Type'} (P : type180 A) (Q : Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (@lem4861313 (type686 A) P Q). Qed.
Lemma lem4861315 {A : Type'} (P : type686 A) (s : A -> Prop) : (term94 A P s) = (term95 A P s).
Proof. exact (@lem4861314 A (term78 A P s) (term59 A P s)). Qed.
Lemma lem4861316 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term96 A P s u) = (term76 A P u s).
Proof. exact (eq_refl (term96 A P s u)). Qed.
Lemma lem4861317 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term78 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4861316 A P u s)). Qed.
Lemma lem4861318 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4861319 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term80 A P s).
Proof. exact (MK_COMB (@lem4861318 A) (@lem4861317 A P s)). Qed.
Lemma lem4861320 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861321 {A : Type'} (P : type686 A) (s : A -> Prop) : (term99 A P s) = (term89 A P s).
Proof. exact (MK_COMB (@lem4861320) (@lem4861319 A P s)). Qed.
Lemma lem4861322 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term59 A P s).
Proof. exact (eq_refl (term59 A P s)). Qed.
Lemma lem4861323 {A : Type'} (P : type686 A) (s : A -> Prop) : (term94 A P s) = (term91 A P s).
Proof. exact (MK_COMB (@lem4861321 A P s) (@lem4861322 A P s)). Qed.
Lemma lem4861324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861325 {A : Type'} (P : type686 A) (s : A -> Prop) : (term100 A P s) = (term101 A P s).
Proof. exact (MK_COMB (@lem4861324) (@lem4861323 A P s)). Qed.
Lemma lem4861326 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term96 A P s u) = (term76 A P u s).
Proof. exact (eq_refl (term96 A P s u)). Qed.
Lemma lem4861327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861328 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) : (term102 A P s u) = (term103 A P u s).
Proof. exact (MK_COMB (@lem4861327) (@lem4861326 A P u s)). Qed.
Lemma lem4861329 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term59 A P s).
Proof. exact (eq_refl (term59 A P s)). Qed.
Lemma lem4861330 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term104 A u P s) = (term105 A u P s).
Proof. exact (MK_COMB (@lem4861328 A P u s) (@lem4861329 A P s)). Qed.
Lemma lem4861331 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term107 A P s).
Proof. exact (fun_ext (fun u : type686 A => @lem4861330 A u P s)). Qed.
Lemma lem4861332 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4861333 {A : Type'} (P : type686 A) (s : A -> Prop) : (term95 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4861332 A) (@lem4861331 A P s)). Qed.
Lemma lem4861334 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term94 A P s) = (term95 A P s)) = ((term91 A P s) = (term108 A P s)).
Proof. exact (MK_COMB (@lem4861325 A P s) (@lem4861333 A P s)). Qed.
Lemma lem4861335 {A : Type'} (P : type686 A) (s : A -> Prop) : (term91 A P s) = (term108 A P s).
Proof. exact (EQ_MP (@lem4861334 A P s) (@lem4861315 A P s)). Qed.
Lemma lem4861386 {A : Type'} (P : type686 A) (s : A -> Prop) : (term90 A P s) = (term108 A P s).
Proof. exact (TRANS (@lem4861311 A P s) (@lem4861335 A P s)). Qed.
Lemma lem4861387 {A : Type'} (P : type686 A) (s : A -> Prop) : (term108 A P s) = (term90 A P s).
Proof. exact (SYM (@lem4861386 A P s)). Qed.
Lemma lem4861388 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term76 A P u s.
Proof. exact (h1). Qed.
Lemma lem4861389 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term73 A P u s.
Proof. exact (h1). Qed.
Lemma lem4861390 {A : Type'} (u : type686 A) (h1 : @ARBITRARY A u) : @ARBITRARY A u.
Proof. exact (h1). Qed.
Lemma lem4861391 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term73 A P u s.
Proof. exact (h1). Qed.
Lemma lem4861392 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (@UNIONS A u) = s.
Proof. exact (h1). Qed.
Lemma lem4861393 {A : Type'} (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : s = (@UNIONS A u).
Proof. exact (SYM (@lem4861392 A u s h1)). Qed.
Lemma lem4861394 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term69 A u P) : term69 A u P.
Proof. exact (h1). Qed.
Lemma lem4861395 {A : Type'} (u : type686 A) (P : type686 A) : (term109 A u P) = (term109 A u P).
Proof. exact (eq_refl (term109 A u P)). Qed.
Lemma lem4861396 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term110 A u P s) = (term111 A P u).
Proof. exact (MK_COMB (@lem4861395 A u P) (@lem4861393 A u s h1)). Qed.
Lemma lem4861397 {A : Type'} (P : type686 A) (u : type686 A) : (term111 A P u) = (term112 A P u).
Proof. exact (eq_refl (term111 A P u)). Qed.
Lemma lem4861398 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term113 A u P s) = (term113 A u P s).
Proof. exact (eq_refl (term113 A u P s)). Qed.
Lemma lem4861399 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term111 A P u)) = ((term110 A u P s) = (term112 A P u)).
Proof. exact (MK_COMB (@lem4861398 A u P s) (@lem4861397 A P u)). Qed.
Lemma lem4861400 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term110 A u P s) = (term114 A u P s).
Proof. exact (eq_refl (term110 A u P s)). Qed.
Lemma lem4861401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861402 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term113 A u P s) = (term115 A u P s).
Proof. exact (MK_COMB (@lem4861401) (@lem4861400 A u P s)). Qed.
Lemma lem4861403 {A : Type'} (P : type686 A) (u : type686 A) : (term112 A P u) = (term112 A P u).
Proof. exact (eq_refl (term112 A P u)). Qed.
Lemma lem4861404 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term112 A P u)) = ((term114 A u P s) = (term112 A P u)).
Proof. exact (MK_COMB (@lem4861402 A u P s) (@lem4861403 A P u)). Qed.
Lemma lem4861405 {A : Type'} (s : A -> Prop) (P : type686 A) (u : type686 A) : ((term110 A u P s) = (term111 A P u)) = ((term114 A u P s) = (term112 A P u)).
Proof. exact (TRANS (@lem4861399 A s P u) (@lem4861404 A s P u)). Qed.
Lemma lem4861406 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term114 A u P s) = (term112 A P u).
Proof. exact (EQ_MP (@lem4861405 A s P u) (@lem4861396 A P u s h1)). Qed.
Lemma lem4861407 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : (@UNIONS A u) = s) : (term112 A P u) = (term114 A u P s).
Proof. exact (SYM (@lem4861406 A P u s h1)). Qed.
Lemma lem4861409 {A : Type'} (P : Prop) (Q : A -> Prop) : (term35 A P Q) = (term36 A P Q).
Proof. exact (EQ_MP (@lem4861048 A P Q) (@lem4861047 A P Q)). Qed.
Lemma lem4861410 {A : Type'} (P : Prop) (Q : type180 A) : (term116 A P Q) = (term117 A P Q).
Proof. exact (@lem4861409 (type686 A) P Q). Qed.
Lemma lem4861411 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term118 A u P c) = (term119 A u P c).
Proof. exact (@lem4861410 A (@IN (A -> Prop) c u) (term120 A P c)). Qed.
Lemma lem4861412 {A : Type'} (P : type686 A) (u : type686 A) (c : A -> Prop) : (term121 A P c u) = (term122 A P u c).
Proof. exact (eq_refl (term121 A P c u)). Qed.
Lemma lem4861413 {A : Type'} (P : type686 A) (c : A -> Prop) : (term123 A P c) = (term120 A P c).
Proof. exact (fun_ext (fun u : type686 A => @lem4861412 A P u c)). Qed.
Lemma lem4861414 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4861415 {A : Type'} (P : type686 A) (c : A -> Prop) : (term124 A P c) = (term59 A P c).
Proof. exact (MK_COMB (@lem4861414 A) (@lem4861413 A P c)). Qed.
Lemma lem4861416 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4861417 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term118 A u P c) = (term65 A u P c).
Proof. exact (MK_COMB (@lem4861416 A c u) (@lem4861415 A P c)). Qed.
Lemma lem4861418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861419 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term125 A u P c) = (term126 A u P c).
Proof. exact (MK_COMB (@lem4861418) (@lem4861417 A u P c)). Qed.
Lemma lem4861420 {A : Type'} (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term121 A P c u') = (term122 A P u' c).
Proof. exact (eq_refl (term121 A P c u')). Qed.
Lemma lem4861421 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4861422 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term127 A u P c u') = (term128 A u P u' c).
Proof. exact (MK_COMB (@lem4861421 A c u) (@lem4861420 A P u' c)). Qed.
Lemma lem4861423 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term129 A u P c) = (term130 A u P c).
Proof. exact (fun_ext (fun u' : type686 A => @lem4861422 A u P u' c)). Qed.
Lemma lem4861424 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4861425 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term119 A u P c) = (term131 A u P c).
Proof. exact (MK_COMB (@lem4861424 A) (@lem4861423 A u P c)). Qed.
Lemma lem4861426 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : ((term118 A u P c) = (term119 A u P c)) = ((term65 A u P c) = (term131 A u P c)).
Proof. exact (MK_COMB (@lem4861419 A u P c) (@lem4861425 A u P c)). Qed.
Lemma lem4861427 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term65 A u P c) = (term131 A u P c).
Proof. exact (EQ_MP (@lem4861426 A u P c) (@lem4861411 A u P c)). Qed.
Lemma lem4861428 {A : Type'} (u : type686 A) (P : type686 A) : (term67 A u P) = (term132 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4861427 A u P c)). Qed.
Lemma lem4861429 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861430 {A : Type'} (u : type686 A) (P : type686 A) : (term69 A u P) = (term133 A u P).
Proof. exact (MK_COMB (@lem4861429 A) (@lem4861428 A u P)). Qed.
Lemma lem4861431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861432 {A : Type'} (u : type686 A) (P : type686 A) : (term134 A u P) = (term135 A u P).
Proof. exact (MK_COMB (@lem4861431) (@lem4861430 A u P)). Qed.
Lemma lem4861433 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4861434 {A : Type'} (P : type686 A) (u : type686 A) : (term112 A P u) = (term137 A P u).
Proof. exact (MK_COMB (@lem4861432 A u P) (@lem4861433 A P u)). Qed.
Lemma lem4861435 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term112 A P u).
Proof. exact (SYM (@lem4861434 A P u)). Qed.
Lemma lem4861439 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem4861042 A B P) (@lem4861041 A B P)). Qed.
Lemma lem4861440 {A : Type'} (P : type599 A) : (term138 A P) = (term139 A P).
Proof. exact (@lem4861439 (A -> Prop) (type686 A) P). Qed.
Lemma lem4861441 {A : Type'} (u : type686 A) (P : type686 A) : (term140 A u P) = (term141 A u P).
Proof. exact (@lem4861440 A (term142 A u P)). Qed.
Lemma lem4861442 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term143 A u P c) = (term130 A u P c).
Proof. exact (eq_refl (term143 A u P c)). Qed.
Lemma lem4861443 {A : Type'} (u' : type686 A) : u' = u'.
Proof. exact (eq_refl u'). Qed.
Lemma lem4861444 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) (u' : type686 A) : (term144 A u P c u') = (term145 A u P c u').
Proof. exact (MK_COMB (@lem4861442 A u P c) (@lem4861443 A u')). Qed.
Lemma lem4861445 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term145 A u P c u') = (term128 A u P u' c).
Proof. exact (eq_refl (term145 A u P c u')). Qed.
Lemma lem4861446 {A : Type'} (u : type686 A) (P : type686 A) (u' : type686 A) (c : A -> Prop) : (term144 A u P c u') = (term128 A u P u' c).
Proof. exact (TRANS (@lem4861444 A u P c u') (@lem4861445 A u P u' c)). Qed.
Lemma lem4861447 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term146 A u P c) = (term130 A u P c).
Proof. exact (fun_ext (fun u' : type686 A => @lem4861446 A u P u' c)). Qed.
Lemma lem4861448 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4861449 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term147 A u P c) = (term131 A u P c).
Proof. exact (MK_COMB (@lem4861448 A) (@lem4861447 A u P c)). Qed.
Lemma lem4861450 {A : Type'} (u : type686 A) (P : type686 A) : (term148 A u P) = (term132 A u P).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4861449 A u P c)). Qed.
Lemma lem4861451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861452 {A : Type'} (u : type686 A) (P : type686 A) : (term140 A u P) = (term133 A u P).
Proof. exact (MK_COMB (@lem4861451 A) (@lem4861450 A u P)). Qed.
Lemma lem4861453 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861454 {A : Type'} (u : type686 A) (P : type686 A) : (term149 A u P) = (term150 A u P).
Proof. exact (MK_COMB (@lem4861453) (@lem4861452 A u P)). Qed.
Lemma lem4861455 {A : Type'} (u : type686 A) (P : type686 A) (c : A -> Prop) : (term143 A u P c) = (term130 A u P c).
Proof. exact (eq_refl (term143 A u P c)). Qed.
Lemma lem4861456 {A : Type'} (u' : type639 A) (c : A -> Prop) : (u' c) = (u' c).
Proof. exact (eq_refl (u' c)). Qed.
Lemma lem4861457 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term151 A u P u' c) = (term152 A u P u' c).
Proof. exact (MK_COMB (@lem4861455 A u P c) (@lem4861456 A u' c)). Qed.
Lemma lem4861458 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term152 A u P u' c) = (term153 A u P u' c).
Proof. exact (eq_refl (term152 A u P u' c)). Qed.
Lemma lem4861459 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) (c : A -> Prop) : (term151 A u P u' c) = (term153 A u P u' c).
Proof. exact (TRANS (@lem4861457 A u P u' c) (@lem4861458 A u P u' c)). Qed.
Lemma lem4861460 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term154 A u P u') = (term155 A u P u').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4861459 A u P u' c)). Qed.
Lemma lem4861461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861462 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term156 A u P u') = (term157 A u P u').
Proof. exact (MK_COMB (@lem4861461 A) (@lem4861460 A u P u')). Qed.
Lemma lem4861463 {A : Type'} (u : type686 A) (P : type686 A) : (term158 A u P) = (term159 A u P).
Proof. exact (fun_ext (fun u' : type639 A => @lem4861462 A u P u')). Qed.
Lemma lem4861464 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4861465 {A : Type'} (u : type686 A) (P : type686 A) : (term141 A u P) = (term160 A u P).
Proof. exact (MK_COMB (@lem4861464 A) (@lem4861463 A u P)). Qed.
Lemma lem4861466 {A : Type'} (u : type686 A) (P : type686 A) : ((term140 A u P) = (term141 A u P)) = ((term133 A u P) = (term160 A u P)).
Proof. exact (MK_COMB (@lem4861454 A u P) (@lem4861465 A u P)). Qed.
Lemma lem4861467 {A : Type'} (u : type686 A) (P : type686 A) : (term133 A u P) = (term160 A u P).
Proof. exact (EQ_MP (@lem4861466 A u P) (@lem4861441 A u P)). Qed.
Lemma lem4861490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861491 {A : Type'} (u : type686 A) (P : type686 A) : (term135 A u P) = (term161 A u P).
Proof. exact (MK_COMB (@lem4861490) (@lem4861467 A u P)). Qed.
Lemma lem4861508 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4861509 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term162 A P u).
Proof. exact (MK_COMB (@lem4861491 A u P) (@lem4861508 A P u)). Qed.
Lemma lem4861511 {A : Type'} (P : A -> Prop) (Q : Prop) : (term27 A P Q) = (term28 A P Q).
Proof. exact (EQ_MP (@lem4861039 A P Q) (@lem4861038 A P Q)). Qed.
Lemma lem4861512 {A : Type'} (P : type141 A) (Q : Prop) : (term163 A P Q) = (term164 A P Q).
Proof. exact (@lem4861511 (type639 A) P Q). Qed.
Lemma lem4861513 {A : Type'} (P : type686 A) (u : type686 A) : (term165 A P u) = (term166 A P u).
Proof. exact (@lem4861512 A (term159 A u P) (term136 A P u)). Qed.
Lemma lem4861514 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term167 A u P u') = (term157 A u P u').
Proof. exact (eq_refl (term167 A u P u')). Qed.
Lemma lem4861515 {A : Type'} (u : type686 A) (P : type686 A) : (term168 A u P) = (term159 A u P).
Proof. exact (fun_ext (fun u' : type639 A => @lem4861514 A u P u')). Qed.
Lemma lem4861516 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4861517 {A : Type'} (u : type686 A) (P : type686 A) : (term169 A u P) = (term160 A u P).
Proof. exact (MK_COMB (@lem4861516 A) (@lem4861515 A u P)). Qed.
Lemma lem4861518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861519 {A : Type'} (u : type686 A) (P : type686 A) : (term170 A u P) = (term161 A u P).
Proof. exact (MK_COMB (@lem4861518) (@lem4861517 A u P)). Qed.
Lemma lem4861520 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4861521 {A : Type'} (P : type686 A) (u : type686 A) : (term165 A P u) = (term162 A P u).
Proof. exact (MK_COMB (@lem4861519 A u P) (@lem4861520 A P u)). Qed.
Lemma lem4861522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861523 {A : Type'} (P : type686 A) (u : type686 A) : (term171 A P u) = (term172 A P u).
Proof. exact (MK_COMB (@lem4861522) (@lem4861521 A P u)). Qed.
Lemma lem4861524 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term167 A u P u') = (term157 A u P u').
Proof. exact (eq_refl (term167 A u P u')). Qed.
Lemma lem4861525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861526 {A : Type'} (u : type686 A) (P : type686 A) (u' : type639 A) : (term173 A u P u') = (term174 A u P u').
Proof. exact (MK_COMB (@lem4861525) (@lem4861524 A u P u')). Qed.
Lemma lem4861527 {A : Type'} (P : type686 A) (u : type686 A) : (term136 A P u) = (term136 A P u).
Proof. exact (eq_refl (term136 A P u)). Qed.
Lemma lem4861528 {A : Type'} (u' : type639 A) (P : type686 A) (u : type686 A) : (term175 A u' P u) = (term176 A u' P u).
Proof. exact (MK_COMB (@lem4861526 A u P u') (@lem4861527 A P u)). Qed.
Lemma lem4861529 {A : Type'} (P : type686 A) (u : type686 A) : (term177 A P u) = (term178 A P u).
Proof. exact (fun_ext (fun u' : type639 A => @lem4861528 A u' P u)). Qed.
Lemma lem4861530 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4861531 {A : Type'} (P : type686 A) (u : type686 A) : (term166 A P u) = (term179 A P u).
Proof. exact (MK_COMB (@lem4861530 A) (@lem4861529 A P u)). Qed.
Lemma lem4861532 {A : Type'} (P : type686 A) (u : type686 A) : ((term165 A P u) = (term166 A P u)) = ((term162 A P u) = (term179 A P u)).
Proof. exact (MK_COMB (@lem4861523 A P u) (@lem4861531 A P u)). Qed.
Lemma lem4861533 {A : Type'} (P : type686 A) (u : type686 A) : (term162 A P u) = (term179 A P u).
Proof. exact (EQ_MP (@lem4861532 A P u) (@lem4861513 A P u)). Qed.
Lemma lem4861574 {A : Type'} (P : type686 A) (u : type686 A) : (term137 A P u) = (term179 A P u).
Proof. exact (TRANS (@lem4861509 A P u) (@lem4861533 A P u)). Qed.
Lemma lem4861575 {A : Type'} (P : type686 A) (u : type686 A) : (term179 A P u) = (term137 A P u).
Proof. exact (SYM (@lem4861574 A P u)). Qed.
Lemma lem4861576 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (h1 : term157 A u P f) : term157 A u P f.
Proof. exact (h1). Qed.
Lemma lem4861577 {A : Type'} (s : type686 A) : term180 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4861578 {A : Type'} (s : type686 A) : (term180 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term180 A s)). Qed.
Lemma lem4861649 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4861578 A s) (@lem4861577 A s)). Qed.
Lemma lem4861650 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4861649 A s). Qed.
Lemma lem4861651 {A : Type'} (u : type686 A) (f : type639 A) : (term181 A u f) = True.
Proof. exact (@lem4861650 A (term182 A u f)). Qed.
Lemma lem4861652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4861653 {A : Type'} (u : type686 A) (f : type639 A) : (term183 A u f) = (and True).
Proof. exact (MK_COMB (@lem4861652) (@lem4861651 A u f)). Qed.
Lemma lem4861739 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term184 A P f u) = (term184 A P f u).
Proof. exact (eq_refl (term184 A P f u)). Qed.
Lemma lem4861740 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term185 A P f u) = (term186 A P f u).
Proof. exact (MK_COMB (@lem4861653 A u f) (@lem4861739 A P f u)). Qed.
Lemma lem4861742 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4861743 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term186 A P f u) = (term184 A P f u).
Proof. exact (@lem4861742 (term184 A P f u)). Qed.
Lemma lem4861829 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term185 A P f u) = (term184 A P f u).
Proof. exact (TRANS (@lem4861740 A P f u) (@lem4861743 A P f u)). Qed.
Lemma lem4861830 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term184 A P f u) = (term185 A P f u).
Proof. exact (SYM (@lem4861829 A P f u)). Qed.
Lemma lem4861834 {_87967 _87968 : Type'} (s : _87968 -> Prop) (P : _87967 -> Prop) (f : _87968 -> _87967) : (term22 _87967 _87968 f s P) = (term23 _87967 _87968 s P f).
Proof. exact (EQ_MP (@lem4861033 _87967 _87968 s P f) (@lem4861032 _87967 _87968 P f s)). Qed.
Lemma lem4861835 {A : Type'} (s : type1171 A) (P : type686 A) (f : type1170 A) : (term187 A f s P) = (term188 A s P f).
Proof. exact (@lem4861834 (A -> Prop) (type1643 A) s P f). Qed.
Lemma lem4861836 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term189 A u f P) = (term190 A u f P).
Proof. exact (@lem4861835 A (term191 A u f) P (@snd (A -> Prop) (A -> Prop))). Qed.
Lemma lem4861838 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term17 _88961 _88962 _89106 P f Q) = (term18 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem4861020 _88961 _88962 _89106 P Q f) (@lem4861019 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4861839 {A : Type'} (P : type639 A) (Q : type1171 A) (f : type637 A) : (term192 A P f Q) = (term193 A P Q f).
Proof. exact (@lem4861838 (A -> Prop) (A -> Prop) (type1643 A) P Q f). Qed.
Lemma lem4861840 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term194 A u f P) = (term195 A u f P).
Proof. exact (@lem4861839 A (term196 A u f) (term197 A P) (@pair (A -> Prop) (A -> Prop))). Qed.
Lemma lem4861841 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term198 A u f s) = (term199 A u f s).
Proof. exact (eq_refl (term198 A u f s)). Qed.
Lemma lem4861842 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4861843 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term200 A u f s t) = (term201 A u f s t).
Proof. exact (MK_COMB (@lem4861841 A u f s) (@lem4861842 A t)). Qed.
Lemma lem4861844 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term201 A u f s t) = (term202 A u t f s).
Proof. exact (eq_refl (term201 A u f s t)). Qed.
Lemma lem4861845 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term200 A u f s t) = (term202 A u t f s).
Proof. exact (TRANS (@lem4861843 A u f s t) (@lem4861844 A u t f s)). Qed.
Lemma lem4861846 {A : Type'} (GEN_PVAR_212 : type1643 A) : (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212) = (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212).
Proof. exact (eq_refl (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212)). Qed.
Lemma lem4861847 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term203 A GEN_PVAR_212 u f s t) = (term204 A GEN_PVAR_212 u t f s).
Proof. exact (MK_COMB (@lem4861846 A GEN_PVAR_212) (@lem4861845 A u t f s)). Qed.
Lemma lem4861848 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@pair (A -> Prop) (A -> Prop) s t) = (@pair (A -> Prop) (A -> Prop) s t).
Proof. exact (eq_refl (@pair (A -> Prop) (A -> Prop) s t)). Qed.
Lemma lem4861849 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term205 A GEN_PVAR_212 u f s t) = (term206 A GEN_PVAR_212 u f s t).
Proof. exact (MK_COMB (@lem4861847 A GEN_PVAR_212 u t f s) (@lem4861848 A s t)). Qed.
Lemma lem4861850 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term207 A GEN_PVAR_212 u f s) = (term208 A GEN_PVAR_212 u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4861849 A GEN_PVAR_212 u f s t)). Qed.
Lemma lem4861851 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4861852 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term209 A GEN_PVAR_212 u f s) = (term210 A GEN_PVAR_212 u f s).
Proof. exact (MK_COMB (@lem4861851 A) (@lem4861850 A GEN_PVAR_212 u f s)). Qed.
Lemma lem4861853 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) : (term211 A GEN_PVAR_212 u f) = (term212 A GEN_PVAR_212 u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861852 A GEN_PVAR_212 u f s)). Qed.
Lemma lem4861854 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4861855 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) : (term213 A GEN_PVAR_212 u f) = (term214 A GEN_PVAR_212 u f).
Proof. exact (MK_COMB (@lem4861854 A) (@lem4861853 A GEN_PVAR_212 u f)). Qed.
Lemma lem4861856 {A : Type'} (u : type686 A) (f : type639 A) : (term215 A u f) = (term216 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_212 : type1643 A => @lem4861855 A GEN_PVAR_212 u f)). Qed.
Lemma lem4861857 {A : Type'} : (@GSPEC (prod (A -> Prop) (A -> Prop))) = (@GSPEC (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@GSPEC (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4861858 {A : Type'} (u : type686 A) (f : type639 A) : (term217 A u f) = (term191 A u f).
Proof. exact (MK_COMB (@lem4861857 A) (@lem4861856 A u f)). Qed.
Lemma lem4861859 {A : Type'} (x : type1643 A) : (@IN (prod (A -> Prop) (A -> Prop)) x) = (@IN (prod (A -> Prop) (A -> Prop)) x).
Proof. exact (eq_refl (@IN (prod (A -> Prop) (A -> Prop)) x)). Qed.
Lemma lem4861860 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term218 A x u f) = (term219 A x u f).
Proof. exact (MK_COMB (@lem4861859 A x) (@lem4861858 A u f)). Qed.
Lemma lem4861861 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861862 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term220 A x u f) = (term221 A x u f).
Proof. exact (MK_COMB (@lem4861861) (@lem4861860 A x u f)). Qed.
Lemma lem4861863 {A : Type'} (P : type686 A) (x : type1643 A) : (term222 A P x) = (term223 A P x).
Proof. exact (eq_refl (term222 A P x)). Qed.
Lemma lem4861864 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (x : type1643 A) : (term224 A u f P x) = (term225 A u f P x).
Proof. exact (MK_COMB (@lem4861862 A x u f) (@lem4861863 A P x)). Qed.
Lemma lem4861865 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term226 A u f P) = (term227 A u f P).
Proof. exact (fun_ext (fun x : type1643 A => @lem4861864 A u f P x)). Qed.
Lemma lem4861866 {A : Type'} : (@all (prod (A -> Prop) (A -> Prop))) = (@all (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@all (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4861867 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term194 A u f P) = (term190 A u f P).
Proof. exact (MK_COMB (@lem4861866 A) (@lem4861865 A u f P)). Qed.
Lemma lem4861868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4861869 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term228 A u f P) = (term229 A u f P).
Proof. exact (MK_COMB (@lem4861868) (@lem4861867 A u f P)). Qed.
Lemma lem4861870 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term198 A u f s) = (term199 A u f s).
Proof. exact (eq_refl (term198 A u f s)). Qed.
Lemma lem4861871 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4861872 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term200 A u f s t) = (term201 A u f s t).
Proof. exact (MK_COMB (@lem4861870 A u f s) (@lem4861871 A t)). Qed.
Lemma lem4861873 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term201 A u f s t) = (term202 A u t f s).
Proof. exact (eq_refl (term201 A u f s t)). Qed.
Lemma lem4861874 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term200 A u f s t) = (term202 A u t f s).
Proof. exact (TRANS (@lem4861872 A u f s t) (@lem4861873 A u t f s)). Qed.
Lemma lem4861875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4861876 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term230 A u f s t) = (term231 A u t f s).
Proof. exact (MK_COMB (@lem4861875) (@lem4861874 A u t f s)). Qed.
Lemma lem4861877 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term232 A P s t) = (term233 A P s t).
Proof. exact (eq_refl (term232 A P s t)). Qed.
Lemma lem4861878 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term234 A u f P s t) = (term235 A u f P s t).
Proof. exact (MK_COMB (@lem4861876 A u t f s) (@lem4861877 A P s t)). Qed.
Lemma lem4861879 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) : (term236 A u f P s) = (term237 A u f P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4861878 A u f P s t)). Qed.
Lemma lem4861880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861881 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (s : A -> Prop) : (term238 A u f P s) = (term239 A u f P s).
Proof. exact (MK_COMB (@lem4861880 A) (@lem4861879 A u f P s)). Qed.
Lemma lem4861882 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term240 A u f P) = (term241 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861881 A u f P s)). Qed.
Lemma lem4861883 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861884 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term195 A u f P) = (term242 A u f P).
Proof. exact (MK_COMB (@lem4861883 A) (@lem4861882 A u f P)). Qed.
Lemma lem4861885 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : ((term194 A u f P) = (term195 A u f P)) = ((term190 A u f P) = (term242 A u f P)).
Proof. exact (MK_COMB (@lem4861869 A u f P) (@lem4861884 A u f P)). Qed.
Lemma lem4861886 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term190 A u f P) = (term242 A u f P).
Proof. exact (EQ_MP (@lem4861885 A u f P) (@lem4861840 A u f P)). Qed.
Lemma lem4861891 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term189 A u f P) = (term242 A u f P).
Proof. exact (TRANS (@lem4861836 A u f P) (@lem4861886 A u f P)). Qed.
Lemma lem4861901 {A B : Type'} (x : A) (y : B) : (term243 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4861902 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term244 A x y) = y.
Proof. exact (@lem4861901 (A -> Prop) (A -> Prop) x y). Qed.
Lemma lem4861903 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term244 A s t) = t.
Proof. exact (@lem4861902 A s t). Qed.
Lemma lem4861904 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4861905 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term233 A P s t) = (P t).
Proof. exact (MK_COMB (@lem4861904 A P) (@lem4861903 A s t)). Qed.
Lemma lem4861906 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term231 A u t f s) = (term231 A u t f s).
Proof. exact (eq_refl (term231 A u t f s)). Qed.
Lemma lem4861907 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term235 A u f P s t) = (term245 A u f s P t).
Proof. exact (MK_COMB (@lem4861906 A u t f s) (@lem4861905 A s P t)). Qed.
Lemma lem4861910 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term237 A u f P s) = (term246 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4861907 A u f s P t)). Qed.
Lemma lem4861911 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861912 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term239 A u f P s) = (term247 A u f s P).
Proof. exact (MK_COMB (@lem4861911 A) (@lem4861910 A u f s P)). Qed.
Lemma lem4861917 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term241 A u f P) = (term248 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4861912 A u f s P)). Qed.
Lemma lem4861918 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4861919 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term242 A u f P) = (term249 A u f P).
Proof. exact (MK_COMB (@lem4861918 A) (@lem4861917 A u f P)). Qed.
Lemma lem4861924 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term189 A u f P) = (term249 A u f P).
Proof. exact (TRANS (@lem4861891 A u f P) (@lem4861919 A u f P)). Qed.
Lemma lem4861925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4861926 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term250 A u f P) = (term251 A u f P).
Proof. exact (MK_COMB (@lem4861925) (@lem4861924 A u f P)). Qed.
Lemma lem4861939 {A : Type'} (f : type639 A) (u : type686 A) : ((term252 A u f) = (@UNIONS A u)) = ((term252 A u f) = (@UNIONS A u)).
Proof. exact (eq_refl ((term252 A u f) = (@UNIONS A u))). Qed.
Lemma lem4861940 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term184 A P f u) = (term253 A P f u).
Proof. exact (MK_COMB (@lem4861926 A u f P) (@lem4861939 A f u)). Qed.
Lemma lem4861943 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term253 A P f u) = (term184 A P f u).
Proof. exact (SYM (@lem4861940 A P f u)). Qed.
Lemma lem4861954 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term254 A P f u.
Proof. exact (conj (@lem4861576 A u P f h1) (@lem4861390 A u h2)). Qed.
Lemma lem4861978 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4861979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (@lem4861978 A s t). Qed.
Lemma lem4861980 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term256 A f c) = c) = (term257 A f c).
Proof. exact (@lem4861979 A (term256 A f c) c). Qed.
Lemma lem4861989 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term258 A f c P) = (term258 A f c P).
Proof. exact (eq_refl (term258 A f c P)). Qed.
Lemma lem4861990 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term259 A P f c) = (term260 A P f c).
Proof. exact (MK_COMB (@lem4861989 A f c P) (@lem4861980 A f c)). Qed.
Lemma lem4861993 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4861994 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term262 A P f c) = (term263 A P f c).
Proof. exact (MK_COMB (@lem4861993 A f c) (@lem4861990 A P f c)). Qed.
Lemma lem4861997 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4861998 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term153 A u P f c) = (term264 A u P f c).
Proof. exact (MK_COMB (@lem4861997 A c u) (@lem4861994 A P f c)). Qed.
Lemma lem4862001 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term155 A u P f) = (term265 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4861998 A u P f c)). Qed.
Lemma lem4862002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862003 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term157 A u P f) = (term266 A u P f).
Proof. exact (MK_COMB (@lem4862002 A) (@lem4862001 A u P f)). Qed.
Lemma lem4862008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862009 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term267 A u P f) = (term268 A u P f).
Proof. exact (MK_COMB (@lem4862008) (@lem4862003 A u P f)). Qed.
Lemma lem4862010 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4862011 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term254 A P f u) = (term269 A P f u).
Proof. exact (MK_COMB (@lem4862009 A u P f) (@lem4862010 A u)). Qed.
Lemma lem4862014 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862015 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term270 A P f u) = (term271 A P f u).
Proof. exact (MK_COMB (@lem4862014) (@lem4862011 A P f u)). Qed.
Lemma lem4862028 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term249 A u f P) = (term249 A u f P).
Proof. exact (eq_refl (term249 A u f P)). Qed.
Lemma lem4862029 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term272 A u f P) = (term273 A u f P).
Proof. exact (MK_COMB (@lem4862015 A P f u) (@lem4862028 A u f P)). Qed.
Lemma lem4862032 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term273 A u f P) = (term272 A u f P).
Proof. exact (SYM (@lem4862029 A u f P)). Qed.
Lemma lem4862044 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862045 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4862044 (A -> Prop) P x). Qed.
Lemma lem4862046 {A : Type'} (u : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c u) = (u c).
Proof. exact (@lem4862045 A u c). Qed.
Lemma lem4862047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862048 {A : Type'} (u : type686 A) (c : A -> Prop) : (term63 A c u) = (term274 A u c).
Proof. exact (MK_COMB (@lem4862047) (@lem4862046 A u c)). Qed.
Lemma lem4862060 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862061 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4862060 (A -> Prop) P x). Qed.
Lemma lem4862062 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term275 A c' f c) = (f c c').
Proof. exact (@lem4862061 A (f c) c'). Qed.
Lemma lem4862063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862064 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term276 A c' f c) = (term277 A f c c').
Proof. exact (MK_COMB (@lem4862063) (@lem4862062 A f c c')). Qed.
Lemma lem4862065 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (P c').
Proof. exact (eq_refl (P c')). Qed.
Lemma lem4862066 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term278 A f c P c') = (term279 A f c P c').
Proof. exact (MK_COMB (@lem4862064 A f c c') (@lem4862065 A P c')). Qed.
Lemma lem4862069 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term280 A f c P) = (term281 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4862066 A f c P c')). Qed.
Lemma lem4862070 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862071 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term282 A f c P) = (term283 A f c P).
Proof. exact (MK_COMB (@lem4862070 A) (@lem4862069 A f c P)). Qed.
Lemma lem4862076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862077 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term258 A f c P) = (term284 A f c P).
Proof. exact (MK_COMB (@lem4862076) (@lem4862071 A f c P)). Qed.
Lemma lem4862085 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4862086 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (@lem4862085 A s x). Qed.
Lemma lem4862087 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term287 A x f c) = (term288 A f c x).
Proof. exact (@lem4862086 A (f c) x). Qed.
Lemma lem4862095 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862096 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4862095 (A -> Prop) P x). Qed.
Lemma lem4862097 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term275 A t f c) = (f c t).
Proof. exact (@lem4862096 A (f c) t). Qed.
Lemma lem4862098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862099 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term289 A t f c) = (term290 A f c t).
Proof. exact (MK_COMB (@lem4862098) (@lem4862097 A f c t)). Qed.
Lemma lem4862101 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862102 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4862101 A P x). Qed.
Lemma lem4862103 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4862102 A t x). Qed.
Lemma lem4862104 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term291 A f c x t) = (term292 A f c t x).
Proof. exact (MK_COMB (@lem4862099 A f c t) (@lem4862103 A t x)). Qed.
Lemma lem4862107 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term293 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862104 A f c t x)). Qed.
Lemma lem4862108 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862109 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term288 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4862108 A) (@lem4862107 A f c x)). Qed.
Lemma lem4862114 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term287 A x f c) = (term295 A f c x).
Proof. exact (TRANS (@lem4862087 A f c x) (@lem4862109 A f c x)). Qed.
Lemma lem4862115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862116 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term296 A x f c) = (term297 A f c x).
Proof. exact (MK_COMB (@lem4862115) (@lem4862114 A f c x)). Qed.
Lemma lem4862118 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862119 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4862118 A P x). Qed.
Lemma lem4862120 {A : Type'} (c : A -> Prop) (x : A) : (@IN A x c) = (c x).
Proof. exact (@lem4862119 A c x). Qed.
Lemma lem4862121 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term287 A x f c) = (@IN A x c)) = ((term295 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4862116 A f c x) (@lem4862120 A c x)). Qed.
Lemma lem4862124 {A : Type'} (f : type639 A) (c : A -> Prop) : (term298 A f c) = (term299 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862121 A f c x)). Qed.
Lemma lem4862125 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862126 {A : Type'} (f : type639 A) (c : A -> Prop) : (term257 A f c) = (term300 A f c).
Proof. exact (MK_COMB (@lem4862125 A) (@lem4862124 A f c)). Qed.
Lemma lem4862131 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term260 A P f c) = (term301 A P f c).
Proof. exact (MK_COMB (@lem4862077 A f c P) (@lem4862126 A f c)). Qed.
Lemma lem4862134 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4862135 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term263 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4862134 A f c) (@lem4862131 A P f c)). Qed.
Lemma lem4862138 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term264 A u P f c) = (term303 A u P f c).
Proof. exact (MK_COMB (@lem4862048 A u c) (@lem4862135 A P f c)). Qed.
Lemma lem4862141 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term265 A u P f) = (term304 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4862138 A u P f c)). Qed.
Lemma lem4862142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862143 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term266 A u P f) = (term305 A u P f).
Proof. exact (MK_COMB (@lem4862142 A) (@lem4862141 A u P f)). Qed.
Lemma lem4862148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862149 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term268 A u P f) = (term306 A u P f).
Proof. exact (MK_COMB (@lem4862148) (@lem4862143 A u P f)). Qed.
Lemma lem4862150 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4862151 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term269 A P f u) = (term307 A P f u).
Proof. exact (MK_COMB (@lem4862149 A u P f) (@lem4862150 A u)). Qed.
Lemma lem4862154 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862155 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term271 A P f u) = (term308 A P f u).
Proof. exact (MK_COMB (@lem4862154) (@lem4862151 A P f u)). Qed.
Lemma lem4862169 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862170 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4862169 (A -> Prop) P x). Qed.
Lemma lem4862171 {A : Type'} (u : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s u) = (u s).
Proof. exact (@lem4862170 A u s). Qed.
Lemma lem4862172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862173 {A : Type'} (u : type686 A) (s : A -> Prop) : (term309 A s u) = (term310 A u s).
Proof. exact (MK_COMB (@lem4862172) (@lem4862171 A u s)). Qed.
Lemma lem4862175 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4862176 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4862175 (A -> Prop) P x). Qed.
Lemma lem4862177 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term275 A t f s) = (f s t).
Proof. exact (@lem4862176 A (f s) t). Qed.
Lemma lem4862178 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term202 A u t f s) = (term311 A u f s t).
Proof. exact (MK_COMB (@lem4862173 A u s) (@lem4862177 A f s t)). Qed.
Lemma lem4862181 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862182 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term231 A u t f s) = (term312 A u f s t).
Proof. exact (MK_COMB (@lem4862181) (@lem4862178 A u f s t)). Qed.
Lemma lem4862183 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (P t).
Proof. exact (eq_refl (P t)). Qed.
Lemma lem4862184 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term245 A u f s P t) = (term313 A u f s P t).
Proof. exact (MK_COMB (@lem4862182 A u f s t) (@lem4862183 A P t)). Qed.
Lemma lem4862187 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term246 A u f s P) = (term314 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862184 A u f s P t)). Qed.
Lemma lem4862188 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862189 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term247 A u f s P) = (term315 A u f s P).
Proof. exact (MK_COMB (@lem4862188 A) (@lem4862187 A u f s P)). Qed.
Lemma lem4862194 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term248 A u f P) = (term316 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4862189 A u f s P)). Qed.
Lemma lem4862195 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862196 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term249 A u f P) = (term317 A u f P).
Proof. exact (MK_COMB (@lem4862195 A) (@lem4862194 A u f P)). Qed.
Lemma lem4862201 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term273 A u f P) = (term318 A u f P).
Proof. exact (MK_COMB (@lem4862155 A P f u) (@lem4862196 A u f P)). Qed.
Lemma lem4862204 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term318 A u f P) = (term273 A u f P).
Proof. exact (SYM (@lem4862201 A u f P)). Qed.
Lemma lem4862206 (p : Prop) : p = (term319 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4862207 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term318 A u f P) = (term320 A u f P).
Proof. exact (@lem4862206 (term318 A u f P)). Qed.
Lemma lem4862208 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term320 A u f P) = (term318 A u f P).
Proof. exact (SYM (@lem4862207 A u f P)). Qed.
Lemma lem4862209 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term321 A u f P) : term321 A u f P.
Proof. exact (h1). Qed.
Lemma lem4862212 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term320 A u f P) : term320 A u f P.
Proof. exact (h1). Qed.
Lemma lem4862213 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term322 A u f P.
Proof. exact (fun h0 : term320 A u f P => @lem4862212 A u f P h0). Qed.
Lemma lem4862214 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term322 A u f P) : term322 A u f P.
Proof. exact (h1). Qed.
Lemma lem4862215 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term320 A u f P) : term320 A u f P.
Proof. exact (h1). Qed.
Lemma lem4862216 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term320 A u f P) (h2 : term322 A u f P) : term320 A u f P.
Proof. exact (@lem4862214 A u f P h2 (@lem4862215 A u f P h1)). Qed.
Lemma lem4862217 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term320 A u f P) : term323 A u f P.
Proof. exact (fun h0 : term322 A u f P => @lem4862216 A u f P h1 h0). Qed.
Lemma lem4862218 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term322 A u f P) : term322 A u f P.
Proof. exact (h1). Qed.
Lemma lem4862219 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term320 A u f P) (h2 : term322 A u f P) : term320 A u f P.
Proof. exact (@lem4862217 A u f P h1 (@lem4862218 A u f P h2)). Qed.
Lemma lem4862220 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term322 A u f P) : term322 A u f P.
Proof. exact (fun h0 : term320 A u f P => @lem4862219 A u f P h0 h1). Qed.
Lemma lem4862221 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term324 A u f P.
Proof. exact (fun h0 : term322 A u f P => @lem4862220 A u f P h0). Qed.
Lemma lem4862224 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term322 A u f P.
Proof. exact (@lem4862221 A u f P (@lem4862213 A u f P)). Qed.
Lemma lem4862225 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term322 A u f P.
Proof. exact (@lem4862224 A u f P). Qed.
Lemma lem4862239 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4862240 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term320 A u f P) = (term325 A u f P).
Proof. exact (@lem4862239 (term321 A u f P)). Qed.
Lemma lem4862242 (t : Prop) : (term326 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4862243 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term325 A u f P) = (term318 A u f P).
Proof. exact (@lem4862242 (term318 A u f P)). Qed.
Lemma lem4862246 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term320 A u f P) = (term318 A u f P).
Proof. exact (TRANS (@lem4862240 A u f P) (@lem4862243 A u f P)). Qed.
Lemma lem4862331 {A : Type'} (f : type639 A) (P : type686 A) : (term327 A f P) = (term328 A f P).
Proof. exact (fun_ext (fun u : type686 A => @lem4862246 A u f P)). Qed.
Lemma lem4862332 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4862333 {A : Type'} (f : type639 A) (P : type686 A) : (term329 A f P) = (term330 A f P).
Proof. exact (MK_COMB (@lem4862332 A) (@lem4862331 A f P)). Qed.
Lemma lem4862338 {A : Type'} (P : type686 A) : (term331 A P) = (term332 A P).
Proof. exact (fun_ext (fun f : type639 A => @lem4862333 A f P)). Qed.
Lemma lem4862339 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4862340 {A : Type'} (P : type686 A) : (term333 A P) = (term334 A P).
Proof. exact (MK_COMB (@lem4862339 A) (@lem4862338 A P)). Qed.
Lemma lem4862345 {A : Type'} : (term335 A) = (term336 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4862340 A P)). Qed.
Lemma lem4862346 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4862355 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (MK_COMB (@lem4862346 A) (@lem4862345 A)). Qed.
Lemma lem4862364 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term313 A u f s P t) = (term313 A u f s P t).
Proof. exact (eq_refl (term313 A u f s P t)). Qed.
Lemma lem4862365 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term314 A u f s P) = (term314 A u f s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862364 A u f s P t)). Qed.
Lemma lem4862366 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862367 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (P : type686 A) : (term315 A u f s P) = (term315 A u f s P).
Proof. exact (MK_COMB (@lem4862366 A) (@lem4862365 A u f s P)). Qed.
Lemma lem4862368 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term316 A u f P) = (term316 A u f P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4862367 A u f s P)). Qed.
Lemma lem4862369 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862370 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term317 A u f P) = (term317 A u f P).
Proof. exact (MK_COMB (@lem4862369 A) (@lem4862368 A u f P)). Qed.
Lemma lem4862371 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4862372 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4862377 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term292 A f c t x) = (term292 A f c t x).
Proof. exact (eq_refl (term292 A f c t x)). Qed.
Lemma lem4862378 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term294 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862377 A f c t x)). Qed.
Lemma lem4862379 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862380 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term295 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4862379 A) (@lem4862378 A f c x)). Qed.
Lemma lem4862381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862382 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term297 A f c x) = (term297 A f c x).
Proof. exact (MK_COMB (@lem4862381) (@lem4862380 A f c x)). Qed.
Lemma lem4862383 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = ((term295 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4862382 A f c x) (@lem4862372 A c x)). Qed.
Lemma lem4862384 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term299 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862383 A f c x)). Qed.
Lemma lem4862385 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862386 {A : Type'} (f : type639 A) (c : A -> Prop) : (term300 A f c) = (term300 A f c).
Proof. exact (MK_COMB (@lem4862385 A) (@lem4862384 A f c)). Qed.
Lemma lem4862391 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term279 A f c P c') = (term279 A f c P c').
Proof. exact (eq_refl (term279 A f c P c')). Qed.
Lemma lem4862392 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term281 A f c P) = (term281 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4862391 A f c P c')). Qed.
Lemma lem4862393 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862394 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term283 A f c P) = (term283 A f c P).
Proof. exact (MK_COMB (@lem4862393 A) (@lem4862392 A f c P)). Qed.
Lemma lem4862395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862396 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term284 A f c P) = (term284 A f c P).
Proof. exact (MK_COMB (@lem4862395) (@lem4862394 A f c P)). Qed.
Lemma lem4862397 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term301 A P f c).
Proof. exact (MK_COMB (@lem4862396 A f c P) (@lem4862386 A f c)). Qed.
Lemma lem4862400 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4862401 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4862400 A f c) (@lem4862397 A P f c)). Qed.
Lemma lem4862404 {A : Type'} (u : type686 A) (c : A -> Prop) : (term274 A u c) = (term274 A u c).
Proof. exact (eq_refl (term274 A u c)). Qed.
Lemma lem4862405 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term303 A u P f c).
Proof. exact (MK_COMB (@lem4862404 A u c) (@lem4862401 A P f c)). Qed.
Lemma lem4862406 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term304 A u P f) = (term304 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4862405 A u P f c)). Qed.
Lemma lem4862407 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862408 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term305 A u P f) = (term305 A u P f).
Proof. exact (MK_COMB (@lem4862407 A) (@lem4862406 A u P f)). Qed.
Lemma lem4862409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862410 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term306 A u P f).
Proof. exact (MK_COMB (@lem4862409) (@lem4862408 A u P f)). Qed.
Lemma lem4862411 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term307 A P f u).
Proof. exact (MK_COMB (@lem4862410 A u P f) (@lem4862371 A u)). Qed.
Lemma lem4862412 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4862413 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term308 A P f u) = (term308 A P f u).
Proof. exact (MK_COMB (@lem4862412) (@lem4862411 A P f u)). Qed.
Lemma lem4862414 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term318 A u f P) = (term318 A u f P).
Proof. exact (MK_COMB (@lem4862413 A P f u) (@lem4862370 A u f P)). Qed.
Lemma lem4862415 {A : Type'} (f : type639 A) (P : type686 A) : (term328 A f P) = (term328 A f P).
Proof. exact (fun_ext (fun u : type686 A => @lem4862414 A u f P)). Qed.
Lemma lem4862416 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4862417 {A : Type'} (f : type639 A) (P : type686 A) : (term330 A f P) = (term330 A f P).
Proof. exact (MK_COMB (@lem4862416 A) (@lem4862415 A f P)). Qed.
Lemma lem4862418 {A : Type'} (P : type686 A) : (term332 A P) = (term332 A P).
Proof. exact (fun_ext (fun f : type639 A => @lem4862417 A f P)). Qed.
Lemma lem4862419 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4862420 {A : Type'} (P : type686 A) : (term334 A P) = (term334 A P).
Proof. exact (MK_COMB (@lem4862419 A) (@lem4862418 A P)). Qed.
Lemma lem4862421 {A : Type'} : (term336 A) = (term336 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4862420 A P)). Qed.
Lemma lem4862422 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4862423 {A : Type'} : (term338 A) = (term338 A).
Proof. exact (MK_COMB (@lem4862422 A) (@lem4862421 A)). Qed.
Lemma lem4862498 {A : Type'} : (term337 A) = (term338 A).
Proof. exact (TRANS (@lem4862355 A) (@lem4862423 A)). Qed.
Lemma lem4862499 {A : Type'} : (term338 A) = (term337 A).
Proof. exact (SYM (@lem4862498 A)). Qed.
Lemma lem4862500 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term307 A P f u.
Proof. exact (h1). Qed.
Lemma lem4862503 (p : Prop) : p = (term319 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4862504 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (term339 A P t).
Proof. exact (@lem4862503 (P t)). Qed.
Lemma lem4862505 {A : Type'} (P : type686 A) (t : A -> Prop) : (term339 A P t) = (P t).
Proof. exact (SYM (@lem4862504 A P t)). Qed.
Lemma lem4862506 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term340 A P t) : term340 A P t.
Proof. exact (h1). Qed.
Lemma lem4862515 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term279 A f c P c') = (term341 A f c P c').
Proof. exact (@lem17265 (f c c') (P c')). Qed.
Lemma lem4862516 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term281 A f c P) = (term342 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4862515 A f c P c')). Qed.
Lemma lem4862517 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862518 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term283 A f c P) = (term343 A f c P).
Proof. exact (MK_COMB (@lem4862517 A) (@lem4862516 A f c P)). Qed.
Lemma lem4862527 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term344 A f c t x) = (term345 A f c t x).
Proof. exact (@lem17045 (f c t) (t x)). Qed.
Lemma lem4862530 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term292 A f c t x) = (term292 A f c t x).
Proof. exact (eq_refl (term292 A f c t x)). Qed.
Lemma lem4862531 {A : Type'} (P : type686 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4862532 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term348 A f c x) = (term349 A f c x).
Proof. exact (@lem4862531 A (term294 A f c x)). Qed.
Lemma lem4862533 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4862534 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4862535 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term351 A f c x t) = (term344 A f c t x).
Proof. exact (MK_COMB (@lem4862534) (@lem4862533 A f c t x)). Qed.
Lemma lem4862536 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term351 A f c x t) = (term345 A f c t x).
Proof. exact (TRANS (@lem4862535 A f c t x) (@lem4862527 A f c t x)). Qed.
Lemma lem4862537 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term352 A f c x) = (term353 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862536 A f c t x)). Qed.
Lemma lem4862538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862539 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term349 A f c x) = (term354 A f c x).
Proof. exact (MK_COMB (@lem4862538 A) (@lem4862537 A f c x)). Qed.
Lemma lem4862540 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term348 A f c x) = (term354 A f c x).
Proof. exact (TRANS (@lem4862532 A f c x) (@lem4862539 A f c x)). Qed.
Lemma lem4862541 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term294 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862530 A f c t x)). Qed.
Lemma lem4862542 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862543 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term295 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4862542 A) (@lem4862541 A f c x)). Qed.
Lemma lem4862544 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4862545 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4862546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4862547 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term356 A f c x) = (term357 A f c x).
Proof. exact (MK_COMB (@lem4862546) (@lem4862540 A f c x)). Qed.
Lemma lem4862548 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term358 A f c x) = (term359 A f c x).
Proof. exact (MK_COMB (@lem4862547 A f c x) (@lem4862545 A c x)). Qed.
Lemma lem4862549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4862550 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term360 A f c x) = (term360 A f c x).
Proof. exact (MK_COMB (@lem4862549) (@lem4862543 A f c x)). Qed.
Lemma lem4862551 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term361 A f c x) = (term361 A f c x).
Proof. exact (MK_COMB (@lem4862550 A f c x) (@lem4862544 A c x)). Qed.
Lemma lem4862552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862553 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term362 A f c x) = (term362 A f c x).
Proof. exact (MK_COMB (@lem4862552) (@lem4862551 A f c x)). Qed.
Lemma lem4862554 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term363 A f c x) = (term364 A f c x).
Proof. exact (MK_COMB (@lem4862553 A f c x) (@lem4862548 A f c x)). Qed.
Lemma lem4862555 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = (term363 A f c x).
Proof. exact (@lem17784 (term295 A f c x) (c x)). Qed.
Lemma lem4862556 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = (term364 A f c x).
Proof. exact (TRANS (@lem4862555 A f c x) (@lem4862554 A f c x)). Qed.
Lemma lem4862557 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term365 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862556 A f c x)). Qed.
Lemma lem4862558 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862559 {A : Type'} (f : type639 A) (c : A -> Prop) : (term300 A f c) = (term366 A f c).
Proof. exact (MK_COMB (@lem4862558 A) (@lem4862557 A f c)). Qed.
Lemma lem4862560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862561 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term284 A f c P) = (term367 A f c P).
Proof. exact (MK_COMB (@lem4862560) (@lem4862518 A f c P)). Qed.
Lemma lem4862562 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term368 A P f c).
Proof. exact (MK_COMB (@lem4862561 A f c P) (@lem4862559 A f c)). Qed.
Lemma lem4862564 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4862565 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term369 A P f c).
Proof. exact (MK_COMB (@lem4862564 A f c) (@lem4862562 A P f c)). Qed.
Lemma lem4862567 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4862568 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term371 A u P f c) = (term372 A u P f c).
Proof. exact (MK_COMB (@lem4862567 A u c) (@lem4862565 A P f c)). Qed.
Lemma lem4862569 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term371 A u P f c).
Proof. exact (@lem17265 (u c) (term302 A P f c)). Qed.
Lemma lem4862570 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term372 A u P f c).
Proof. exact (TRANS (@lem4862569 A u P f c) (@lem4862568 A u P f c)). Qed.
Lemma lem4862571 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term304 A u P f) = (term373 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4862570 A u P f c)). Qed.
Lemma lem4862572 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862573 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term305 A u P f) = (term374 A u P f).
Proof. exact (MK_COMB (@lem4862572 A) (@lem4862571 A u P f)). Qed.
Lemma lem4862574 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4862575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862576 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term375 A u P f).
Proof. exact (MK_COMB (@lem4862575) (@lem4862573 A u P f)). Qed.
Lemma lem4862577 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term376 A P f u).
Proof. exact (MK_COMB (@lem4862576 A u P f) (@lem4862574 A u)). Qed.
Lemma lem4862659 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4862660 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (@lem4862659 A P Q). Qed.
Lemma lem4862661 {A : Type'} (f : type639 A) (c : A -> Prop) : (term379 A f c) = (term380 A f c).
Proof. exact (@lem4862660 A (term381 A f c) (term382 A f c)). Qed.
Lemma lem4862662 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term383 A f c x) = (term361 A f c x).
Proof. exact (eq_refl (term383 A f c x)). Qed.
Lemma lem4862663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862664 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term384 A f c x) = (term362 A f c x).
Proof. exact (MK_COMB (@lem4862663) (@lem4862662 A f c x)). Qed.
Lemma lem4862665 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term385 A f c x) = (term359 A f c x).
Proof. exact (eq_refl (term385 A f c x)). Qed.
Lemma lem4862666 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term386 A f c x) = (term364 A f c x).
Proof. exact (MK_COMB (@lem4862664 A f c x) (@lem4862665 A f c x)). Qed.
Lemma lem4862667 {A : Type'} (f : type639 A) (c : A -> Prop) : (term387 A f c) = (term365 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862666 A f c x)). Qed.
Lemma lem4862668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862669 {A : Type'} (f : type639 A) (c : A -> Prop) : (term379 A f c) = (term366 A f c).
Proof. exact (MK_COMB (@lem4862668 A) (@lem4862667 A f c)). Qed.
Lemma lem4862670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862671 {A : Type'} (f : type639 A) (c : A -> Prop) : (term388 A f c) = (term389 A f c).
Proof. exact (MK_COMB (@lem4862670) (@lem4862669 A f c)). Qed.
Lemma lem4862672 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term383 A f c x) = (term361 A f c x).
Proof. exact (eq_refl (term383 A f c x)). Qed.
Lemma lem4862673 {A : Type'} (f : type639 A) (c : A -> Prop) : (term390 A f c) = (term381 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862672 A f c x)). Qed.
Lemma lem4862674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862675 {A : Type'} (f : type639 A) (c : A -> Prop) : (term391 A f c) = (term392 A f c).
Proof. exact (MK_COMB (@lem4862674 A) (@lem4862673 A f c)). Qed.
Lemma lem4862676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862677 {A : Type'} (f : type639 A) (c : A -> Prop) : (term393 A f c) = (term394 A f c).
Proof. exact (MK_COMB (@lem4862676) (@lem4862675 A f c)). Qed.
Lemma lem4862678 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term385 A f c x) = (term359 A f c x).
Proof. exact (eq_refl (term385 A f c x)). Qed.
Lemma lem4862679 {A : Type'} (f : type639 A) (c : A -> Prop) : (term395 A f c) = (term382 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862678 A f c x)). Qed.
Lemma lem4862680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862681 {A : Type'} (f : type639 A) (c : A -> Prop) : (term396 A f c) = (term397 A f c).
Proof. exact (MK_COMB (@lem4862680 A) (@lem4862679 A f c)). Qed.
Lemma lem4862682 {A : Type'} (f : type639 A) (c : A -> Prop) : (term380 A f c) = (term398 A f c).
Proof. exact (MK_COMB (@lem4862677 A f c) (@lem4862681 A f c)). Qed.
Lemma lem4862683 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term379 A f c) = (term380 A f c)) = ((term366 A f c) = (term398 A f c)).
Proof. exact (MK_COMB (@lem4862671 A f c) (@lem4862682 A f c)). Qed.
Lemma lem4862684 {A : Type'} (f : type639 A) (c : A -> Prop) : (term366 A f c) = (term398 A f c).
Proof. exact (EQ_MP (@lem4862683 A f c) (@lem4862661 A f c)). Qed.
Lemma lem4862861 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4862862 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term368 A P f c) = (term399 A P f c).
Proof. exact (MK_COMB (@lem4862861 A f c P) (@lem4862684 A f c)). Qed.
Lemma lem4862863 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4862864 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term369 A P f c) = (term400 A P f c).
Proof. exact (MK_COMB (@lem4862863 A f c) (@lem4862862 A P f c)). Qed.
Lemma lem4862865 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4862866 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term372 A u P f c) = (term401 A u P f c).
Proof. exact (MK_COMB (@lem4862865 A u c) (@lem4862864 A P f c)). Qed.
Lemma lem4862867 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term373 A u P f) = (term402 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4862866 A u P f c)). Qed.
Lemma lem4862868 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4862869 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term374 A u P f) = (term403 A u P f).
Proof. exact (MK_COMB (@lem4862868 A) (@lem4862867 A u P f)). Qed.
Lemma lem4862918 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862919 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term375 A u P f) = (term404 A u P f).
Proof. exact (MK_COMB (@lem4862918) (@lem4862869 A u P f)). Qed.
Lemma lem4862920 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4862921 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term376 A P f u) = (term405 A P f u).
Proof. exact (MK_COMB (@lem4862919 A u P f) (@lem4862920 A u)). Qed.
Lemma lem4862923 {A : Type'} (P : A -> Prop) (Q : Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4862924 {A : Type'} (P : type686 A) (Q : Prop) : (term408 A P Q) = (term409 A P Q).
Proof. exact (@lem4862923 (A -> Prop) P Q). Qed.
Lemma lem4862925 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term410 A f c x) = (term411 A f c x).
Proof. exact (@lem4862924 A (term294 A f c x) (term355 A c x)). Qed.
Lemma lem4862926 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4862927 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term412 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862926 A f c t x)). Qed.
Lemma lem4862928 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862929 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term413 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4862928 A) (@lem4862927 A f c x)). Qed.
Lemma lem4862930 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4862931 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term414 A f c x) = (term360 A f c x).
Proof. exact (MK_COMB (@lem4862930) (@lem4862929 A f c x)). Qed.
Lemma lem4862932 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4862933 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term410 A f c x) = (term361 A f c x).
Proof. exact (MK_COMB (@lem4862931 A f c x) (@lem4862932 A c x)). Qed.
Lemma lem4862934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862935 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term415 A f c x) = (term416 A f c x).
Proof. exact (MK_COMB (@lem4862934) (@lem4862933 A f c x)). Qed.
Lemma lem4862936 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4862937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4862938 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term417 A f c x t) = (term418 A f c t x).
Proof. exact (MK_COMB (@lem4862937) (@lem4862936 A f c t x)). Qed.
Lemma lem4862939 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4862940 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term419 A f t c x) = (term420 A f t c x).
Proof. exact (MK_COMB (@lem4862938 A f c t x) (@lem4862939 A c x)). Qed.
Lemma lem4862941 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term421 A f c x) = (term422 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862940 A f t c x)). Qed.
Lemma lem4862942 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862943 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term411 A f c x) = (term423 A f c x).
Proof. exact (MK_COMB (@lem4862942 A) (@lem4862941 A f c x)). Qed.
Lemma lem4862944 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term410 A f c x) = (term411 A f c x)) = ((term361 A f c x) = (term423 A f c x)).
Proof. exact (MK_COMB (@lem4862935 A f c x) (@lem4862943 A f c x)). Qed.
Lemma lem4862945 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term361 A f c x) = (term423 A f c x).
Proof. exact (EQ_MP (@lem4862944 A f c x) (@lem4862925 A f c x)). Qed.
Lemma lem4862946 {A : Type'} (f : type639 A) (c : A -> Prop) : (term381 A f c) = (term424 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862945 A f c x)). Qed.
Lemma lem4862947 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862948 {A : Type'} (f : type639 A) (c : A -> Prop) : (term392 A f c) = (term425 A f c).
Proof. exact (MK_COMB (@lem4862947 A) (@lem4862946 A f c)). Qed.
Lemma lem4862950 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4862951 {A : Type'} (P : type1364 A) : (term426 A P) = (term427 A P).
Proof. exact (@lem4862950 A (A -> Prop) P). Qed.
Lemma lem4862952 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term429 A f c).
Proof. exact (@lem4862951 A (term430 A f c)). Qed.
Lemma lem4862953 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term431 A f c x) = (term422 A f c x).
Proof. exact (eq_refl (term431 A f c x)). Qed.
Lemma lem4862954 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4862955 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) (t : A -> Prop) : (term432 A f c x t) = (term433 A f c x t).
Proof. exact (MK_COMB (@lem4862953 A f c x) (@lem4862954 A t)). Qed.
Lemma lem4862956 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term433 A f c x t) = (term420 A f t c x).
Proof. exact (eq_refl (term433 A f c x t)). Qed.
Lemma lem4862957 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term432 A f c x t) = (term420 A f t c x).
Proof. exact (TRANS (@lem4862955 A f c x t) (@lem4862956 A f t c x)). Qed.
Lemma lem4862958 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term434 A f c x) = (term422 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4862957 A f t c x)). Qed.
Lemma lem4862959 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4862960 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term435 A f c x) = (term423 A f c x).
Proof. exact (MK_COMB (@lem4862959 A) (@lem4862958 A f c x)). Qed.
Lemma lem4862961 {A : Type'} (f : type639 A) (c : A -> Prop) : (term436 A f c) = (term424 A f c).
Proof. exact (fun_ext (fun x : A => @lem4862960 A f c x)). Qed.
Lemma lem4862962 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862963 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term425 A f c).
Proof. exact (MK_COMB (@lem4862962 A) (@lem4862961 A f c)). Qed.
Lemma lem4862964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862965 {A : Type'} (f : type639 A) (c : A -> Prop) : (term437 A f c) = (term438 A f c).
Proof. exact (MK_COMB (@lem4862964) (@lem4862963 A f c)). Qed.
Lemma lem4862966 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term431 A f c x) = (term422 A f c x).
Proof. exact (eq_refl (term431 A f c x)). Qed.
Lemma lem4862967 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4862968 {A : Type'} (f : type639 A) (c : A -> Prop) (t : type1402 A) (x : A) : (term439 A f c t x) = (term440 A f c t x).
Proof. exact (MK_COMB (@lem4862966 A f c x) (@lem4862967 A t x)). Qed.
Lemma lem4862969 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term440 A f c t x) = (term441 A f t c x).
Proof. exact (eq_refl (term440 A f c t x)). Qed.
Lemma lem4862970 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term439 A f c t x) = (term441 A f t c x).
Proof. exact (TRANS (@lem4862968 A f c t x) (@lem4862969 A f t c x)). Qed.
Lemma lem4862971 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term442 A f c t) = (term443 A f t c).
Proof. exact (fun_ext (fun x : A => @lem4862970 A f t c x)). Qed.
Lemma lem4862972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4862973 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term444 A f c t) = (term445 A f t c).
Proof. exact (MK_COMB (@lem4862972 A) (@lem4862971 A f t c)). Qed.
Lemma lem4862974 {A : Type'} (f : type639 A) (c : A -> Prop) : (term446 A f c) = (term447 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4862973 A f t c)). Qed.
Lemma lem4862975 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4862976 {A : Type'} (f : type639 A) (c : A -> Prop) : (term429 A f c) = (term448 A f c).
Proof. exact (MK_COMB (@lem4862975 A) (@lem4862974 A f c)). Qed.
Lemma lem4862977 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term428 A f c) = (term429 A f c)) = ((term425 A f c) = (term448 A f c)).
Proof. exact (MK_COMB (@lem4862965 A f c) (@lem4862976 A f c)). Qed.
Lemma lem4862978 {A : Type'} (f : type639 A) (c : A -> Prop) : (term425 A f c) = (term448 A f c).
Proof. exact (EQ_MP (@lem4862977 A f c) (@lem4862952 A f c)). Qed.
Lemma lem4862979 {A : Type'} (f : type639 A) (c : A -> Prop) : (term392 A f c) = (term448 A f c).
Proof. exact (TRANS (@lem4862948 A f c) (@lem4862978 A f c)). Qed.
Lemma lem4862980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862981 {A : Type'} (f : type639 A) (c : A -> Prop) : (term394 A f c) = (term449 A f c).
Proof. exact (MK_COMB (@lem4862980) (@lem4862979 A f c)). Qed.
Lemma lem4862982 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4862983 {A : Type'} (f : type639 A) (c : A -> Prop) : (term398 A f c) = (term450 A f c).
Proof. exact (MK_COMB (@lem4862981 A f c) (@lem4862982 A f c)). Qed.
Lemma lem4862985 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4862986 {A : Type'} (P : type421 A) (Q : Prop) : (term453 A P Q) = (term454 A P Q).
Proof. exact (@lem4862985 (type1402 A) P Q). Qed.
Lemma lem4862987 {A : Type'} (f : type639 A) (c : A -> Prop) : (term455 A f c) = (term456 A f c).
Proof. exact (@lem4862986 A (term447 A f c) (term397 A f c)). Qed.
Lemma lem4862988 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term457 A f c t) = (term445 A f t c).
Proof. exact (eq_refl (term457 A f c t)). Qed.
Lemma lem4862989 {A : Type'} (f : type639 A) (c : A -> Prop) : (term458 A f c) = (term447 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4862988 A f t c)). Qed.
Lemma lem4862990 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4862991 {A : Type'} (f : type639 A) (c : A -> Prop) : (term459 A f c) = (term448 A f c).
Proof. exact (MK_COMB (@lem4862990 A) (@lem4862989 A f c)). Qed.
Lemma lem4862992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4862993 {A : Type'} (f : type639 A) (c : A -> Prop) : (term460 A f c) = (term449 A f c).
Proof. exact (MK_COMB (@lem4862992) (@lem4862991 A f c)). Qed.
Lemma lem4862994 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4862995 {A : Type'} (f : type639 A) (c : A -> Prop) : (term455 A f c) = (term450 A f c).
Proof. exact (MK_COMB (@lem4862993 A f c) (@lem4862994 A f c)). Qed.
Lemma lem4862996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4862997 {A : Type'} (f : type639 A) (c : A -> Prop) : (term461 A f c) = (term462 A f c).
Proof. exact (MK_COMB (@lem4862996) (@lem4862995 A f c)). Qed.
Lemma lem4862998 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term457 A f c t) = (term445 A f t c).
Proof. exact (eq_refl (term457 A f c t)). Qed.
Lemma lem4862999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863000 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term463 A f c t) = (term464 A f t c).
Proof. exact (MK_COMB (@lem4862999) (@lem4862998 A f t c)). Qed.
Lemma lem4863001 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4863002 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term465 A t f c) = (term466 A t f c).
Proof. exact (MK_COMB (@lem4863000 A f t c) (@lem4863001 A f c)). Qed.
Lemma lem4863003 {A : Type'} (f : type639 A) (c : A -> Prop) : (term467 A f c) = (term468 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863002 A t f c)). Qed.
Lemma lem4863004 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863005 {A : Type'} (f : type639 A) (c : A -> Prop) : (term456 A f c) = (term469 A f c).
Proof. exact (MK_COMB (@lem4863004 A) (@lem4863003 A f c)). Qed.
Lemma lem4863006 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term455 A f c) = (term456 A f c)) = ((term450 A f c) = (term469 A f c)).
Proof. exact (MK_COMB (@lem4862997 A f c) (@lem4863005 A f c)). Qed.
Lemma lem4863007 {A : Type'} (f : type639 A) (c : A -> Prop) : (term450 A f c) = (term469 A f c).
Proof. exact (EQ_MP (@lem4863006 A f c) (@lem4862987 A f c)). Qed.
Lemma lem4863008 {A : Type'} (f : type639 A) (c : A -> Prop) : (term398 A f c) = (term469 A f c).
Proof. exact (TRANS (@lem4862983 A f c) (@lem4863007 A f c)). Qed.
Lemma lem4863009 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4863010 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term399 A P f c) = (term470 A P f c).
Proof. exact (MK_COMB (@lem4863009 A f c P) (@lem4863008 A f c)). Qed.
Lemma lem4863012 {A : Type'} (P : Prop) (Q : A -> Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4863013 {A : Type'} (P : Prop) (Q : type421 A) : (term473 A P Q) = (term474 A P Q).
Proof. exact (@lem4863012 (type1402 A) P Q). Qed.
Lemma lem4863014 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term475 A P f c) = (term476 A P f c).
Proof. exact (@lem4863013 A (term343 A f c P) (term468 A f c)). Qed.
Lemma lem4863015 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term477 A f c t) = (term466 A t f c).
Proof. exact (eq_refl (term477 A f c t)). Qed.
Lemma lem4863016 {A : Type'} (f : type639 A) (c : A -> Prop) : (term478 A f c) = (term468 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863015 A t f c)). Qed.
Lemma lem4863017 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863018 {A : Type'} (f : type639 A) (c : A -> Prop) : (term479 A f c) = (term469 A f c).
Proof. exact (MK_COMB (@lem4863017 A) (@lem4863016 A f c)). Qed.
Lemma lem4863019 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4863020 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term475 A P f c) = (term470 A P f c).
Proof. exact (MK_COMB (@lem4863019 A f c P) (@lem4863018 A f c)). Qed.
Lemma lem4863021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863022 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term480 A P f c) = (term481 A P f c).
Proof. exact (MK_COMB (@lem4863021) (@lem4863020 A P f c)). Qed.
Lemma lem4863023 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term477 A f c t) = (term466 A t f c).
Proof. exact (eq_refl (term477 A f c t)). Qed.
Lemma lem4863024 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4863025 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term482 A P f c t) = (term483 A P t f c).
Proof. exact (MK_COMB (@lem4863024 A f c P) (@lem4863023 A t f c)). Qed.
Lemma lem4863026 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term484 A P f c) = (term485 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863025 A P t f c)). Qed.
Lemma lem4863027 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863028 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term476 A P f c) = (term486 A P f c).
Proof. exact (MK_COMB (@lem4863027 A) (@lem4863026 A P f c)). Qed.
Lemma lem4863029 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term475 A P f c) = (term476 A P f c)) = ((term470 A P f c) = (term486 A P f c)).
Proof. exact (MK_COMB (@lem4863022 A P f c) (@lem4863028 A P f c)). Qed.
Lemma lem4863030 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term470 A P f c) = (term486 A P f c).
Proof. exact (EQ_MP (@lem4863029 A P f c) (@lem4863014 A P f c)). Qed.
Lemma lem4863031 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term399 A P f c) = (term486 A P f c).
Proof. exact (TRANS (@lem4863010 A P f c) (@lem4863030 A P f c)). Qed.
Lemma lem4863032 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4863033 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term400 A P f c) = (term487 A P f c).
Proof. exact (MK_COMB (@lem4863032 A f c) (@lem4863031 A P f c)). Qed.
Lemma lem4863035 {A : Type'} (P : Prop) (Q : A -> Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4863036 {A : Type'} (P : Prop) (Q : type421 A) : (term473 A P Q) = (term474 A P Q).
Proof. exact (@lem4863035 (type1402 A) P Q). Qed.
Lemma lem4863037 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term488 A P f c) = (term489 A P f c).
Proof. exact (@lem4863036 A (term490 A f c) (term485 A P f c)). Qed.
Lemma lem4863038 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term491 A P f c t) = (term483 A P t f c).
Proof. exact (eq_refl (term491 A P f c t)). Qed.
Lemma lem4863039 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term492 A P f c) = (term485 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863038 A P t f c)). Qed.
Lemma lem4863040 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863041 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term493 A P f c) = (term486 A P f c).
Proof. exact (MK_COMB (@lem4863040 A) (@lem4863039 A P f c)). Qed.
Lemma lem4863042 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4863043 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term488 A P f c) = (term487 A P f c).
Proof. exact (MK_COMB (@lem4863042 A f c) (@lem4863041 A P f c)). Qed.
Lemma lem4863044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863045 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term494 A P f c) = (term495 A P f c).
Proof. exact (MK_COMB (@lem4863044) (@lem4863043 A P f c)). Qed.
Lemma lem4863046 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term491 A P f c t) = (term483 A P t f c).
Proof. exact (eq_refl (term491 A P f c t)). Qed.
Lemma lem4863047 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4863048 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term496 A P f c t) = (term497 A P t f c).
Proof. exact (MK_COMB (@lem4863047 A f c) (@lem4863046 A P t f c)). Qed.
Lemma lem4863049 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term498 A P f c) = (term499 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863048 A P t f c)). Qed.
Lemma lem4863050 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863051 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term489 A P f c) = (term500 A P f c).
Proof. exact (MK_COMB (@lem4863050 A) (@lem4863049 A P f c)). Qed.
Lemma lem4863052 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term488 A P f c) = (term489 A P f c)) = ((term487 A P f c) = (term500 A P f c)).
Proof. exact (MK_COMB (@lem4863045 A P f c) (@lem4863051 A P f c)). Qed.
Lemma lem4863053 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term487 A P f c) = (term500 A P f c).
Proof. exact (EQ_MP (@lem4863052 A P f c) (@lem4863037 A P f c)). Qed.
Lemma lem4863054 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term400 A P f c) = (term500 A P f c).
Proof. exact (TRANS (@lem4863033 A P f c) (@lem4863053 A P f c)). Qed.
Lemma lem4863055 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4863056 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term401 A u P f c) = (term501 A u P f c).
Proof. exact (MK_COMB (@lem4863055 A u c) (@lem4863054 A P f c)). Qed.
Lemma lem4863058 {A : Type'} (P : Prop) (Q : A -> Prop) : (term502 A P Q) = (term503 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4863059 {A : Type'} (P : Prop) (Q : type421 A) : (term504 A P Q) = (term505 A P Q).
Proof. exact (@lem4863058 (type1402 A) P Q). Qed.
Lemma lem4863060 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term506 A u P f c) = (term507 A u P f c).
Proof. exact (@lem4863059 A (term340 A u c) (term499 A P f c)). Qed.
Lemma lem4863061 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term508 A P f c t) = (term497 A P t f c).
Proof. exact (eq_refl (term508 A P f c t)). Qed.
Lemma lem4863062 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term509 A P f c) = (term499 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863061 A P t f c)). Qed.
Lemma lem4863063 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863064 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term510 A P f c) = (term500 A P f c).
Proof. exact (MK_COMB (@lem4863063 A) (@lem4863062 A P f c)). Qed.
Lemma lem4863065 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4863066 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term506 A u P f c) = (term501 A u P f c).
Proof. exact (MK_COMB (@lem4863065 A u c) (@lem4863064 A P f c)). Qed.
Lemma lem4863067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863068 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term511 A u P f c) = (term512 A u P f c).
Proof. exact (MK_COMB (@lem4863067) (@lem4863066 A u P f c)). Qed.
Lemma lem4863069 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term508 A P f c t) = (term497 A P t f c).
Proof. exact (eq_refl (term508 A P f c t)). Qed.
Lemma lem4863070 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4863071 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term513 A u P f c t) = (term514 A u P t f c).
Proof. exact (MK_COMB (@lem4863070 A u c) (@lem4863069 A P t f c)). Qed.
Lemma lem4863072 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term515 A u P f c) = (term516 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863071 A u P t f c)). Qed.
Lemma lem4863073 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863074 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term507 A u P f c) = (term517 A u P f c).
Proof. exact (MK_COMB (@lem4863073 A) (@lem4863072 A u P f c)). Qed.
Lemma lem4863075 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term506 A u P f c) = (term507 A u P f c)) = ((term501 A u P f c) = (term517 A u P f c)).
Proof. exact (MK_COMB (@lem4863068 A u P f c) (@lem4863074 A u P f c)). Qed.
Lemma lem4863076 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term501 A u P f c) = (term517 A u P f c).
Proof. exact (EQ_MP (@lem4863075 A u P f c) (@lem4863060 A u P f c)). Qed.
Lemma lem4863077 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term401 A u P f c) = (term517 A u P f c).
Proof. exact (TRANS (@lem4863056 A u P f c) (@lem4863076 A u P f c)). Qed.
Lemma lem4863078 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term402 A u P f) = (term518 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863077 A u P f c)). Qed.
Lemma lem4863079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863080 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term403 A u P f) = (term519 A u P f).
Proof. exact (MK_COMB (@lem4863079 A) (@lem4863078 A u P f)). Qed.
Lemma lem4863082 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4863083 {A : Type'} (P : type611 A) : (term520 A P) = (term521 A P).
Proof. exact (@lem4863082 (A -> Prop) (type1402 A) P). Qed.
Lemma lem4863084 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term522 A u P f) = (term523 A u P f).
Proof. exact (@lem4863083 A (term524 A u P f)). Qed.
Lemma lem4863085 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A u P f c) = (term516 A u P f c).
Proof. exact (eq_refl (term525 A u P f c)). Qed.
Lemma lem4863086 {A : Type'} (t : type1402 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4863087 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) (t : type1402 A) : (term526 A u P f c t) = (term527 A u P f c t).
Proof. exact (MK_COMB (@lem4863085 A u P f c) (@lem4863086 A t)). Qed.
Lemma lem4863088 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term527 A u P f c t) = (term514 A u P t f c).
Proof. exact (eq_refl (term527 A u P f c t)). Qed.
Lemma lem4863089 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term526 A u P f c t) = (term514 A u P t f c).
Proof. exact (TRANS (@lem4863087 A u P f c t) (@lem4863088 A u P t f c)). Qed.
Lemma lem4863090 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term528 A u P f c) = (term516 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4863089 A u P t f c)). Qed.
Lemma lem4863091 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4863092 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A u P f c) = (term517 A u P f c).
Proof. exact (MK_COMB (@lem4863091 A) (@lem4863090 A u P f c)). Qed.
Lemma lem4863093 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term530 A u P f) = (term518 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863092 A u P f c)). Qed.
Lemma lem4863094 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863095 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term522 A u P f) = (term519 A u P f).
Proof. exact (MK_COMB (@lem4863094 A) (@lem4863093 A u P f)). Qed.
Lemma lem4863096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863097 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term531 A u P f) = (term532 A u P f).
Proof. exact (MK_COMB (@lem4863096) (@lem4863095 A u P f)). Qed.
Lemma lem4863098 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A u P f c) = (term516 A u P f c).
Proof. exact (eq_refl (term525 A u P f c)). Qed.
Lemma lem4863099 {A : Type'} (t : type667 A) (c : A -> Prop) : (t c) = (t c).
Proof. exact (eq_refl (t c)). Qed.
Lemma lem4863100 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (t : type667 A) (c : A -> Prop) : (term533 A u P f t c) = (term534 A u P f t c).
Proof. exact (MK_COMB (@lem4863098 A u P f c) (@lem4863099 A t c)). Qed.
Lemma lem4863101 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term534 A u P f t c) = (term535 A u P t f c).
Proof. exact (eq_refl (term534 A u P f t c)). Qed.
Lemma lem4863102 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term533 A u P f t c) = (term535 A u P t f c).
Proof. exact (TRANS (@lem4863100 A u P f t c) (@lem4863101 A u P t f c)). Qed.
Lemma lem4863103 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term536 A u P f t) = (term537 A u P t f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863102 A u P t f c)). Qed.
Lemma lem4863104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863105 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term538 A u P f t) = (term539 A u P t f).
Proof. exact (MK_COMB (@lem4863104 A) (@lem4863103 A u P t f)). Qed.
Lemma lem4863106 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term540 A u P f) = (term541 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4863105 A u P t f)). Qed.
Lemma lem4863107 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4863108 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term523 A u P f) = (term542 A u P f).
Proof. exact (MK_COMB (@lem4863107 A) (@lem4863106 A u P f)). Qed.
Lemma lem4863109 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : ((term522 A u P f) = (term523 A u P f)) = ((term519 A u P f) = (term542 A u P f)).
Proof. exact (MK_COMB (@lem4863097 A u P f) (@lem4863108 A u P f)). Qed.
Lemma lem4863110 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term519 A u P f) = (term542 A u P f).
Proof. exact (EQ_MP (@lem4863109 A u P f) (@lem4863084 A u P f)). Qed.
Lemma lem4863111 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term403 A u P f) = (term542 A u P f).
Proof. exact (TRANS (@lem4863080 A u P f) (@lem4863110 A u P f)). Qed.
Lemma lem4863112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863113 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term404 A u P f) = (term543 A u P f).
Proof. exact (MK_COMB (@lem4863112) (@lem4863111 A u P f)). Qed.
Lemma lem4863114 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4863115 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term405 A P f u) = (term544 A P f u).
Proof. exact (MK_COMB (@lem4863113 A u P f) (@lem4863114 A u)). Qed.
Lemma lem4863117 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4863118 {A : Type'} (P : type149 A) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (@lem4863117 (type667 A) P Q). Qed.
Lemma lem4863119 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term547 A P f u) = (term548 A P f u).
Proof. exact (@lem4863118 A (term541 A u P f) (@ARBITRARY A u)). Qed.
Lemma lem4863120 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term549 A u P f t) = (term539 A u P t f).
Proof. exact (eq_refl (term549 A u P f t)). Qed.
Lemma lem4863121 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term550 A u P f) = (term541 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4863120 A u P t f)). Qed.
Lemma lem4863122 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4863123 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term551 A u P f) = (term542 A u P f).
Proof. exact (MK_COMB (@lem4863122 A) (@lem4863121 A u P f)). Qed.
Lemma lem4863124 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863125 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term552 A u P f) = (term543 A u P f).
Proof. exact (MK_COMB (@lem4863124) (@lem4863123 A u P f)). Qed.
Lemma lem4863126 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4863127 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term547 A P f u) = (term544 A P f u).
Proof. exact (MK_COMB (@lem4863125 A u P f) (@lem4863126 A u)). Qed.
Lemma lem4863128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863129 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term553 A P f u) = (term554 A P f u).
Proof. exact (MK_COMB (@lem4863128) (@lem4863127 A P f u)). Qed.
Lemma lem4863130 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term549 A u P f t) = (term539 A u P t f).
Proof. exact (eq_refl (term549 A u P f t)). Qed.
Lemma lem4863131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863132 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term555 A u P f t) = (term556 A u P t f).
Proof. exact (MK_COMB (@lem4863131) (@lem4863130 A u P t f)). Qed.
Lemma lem4863133 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4863134 {A : Type'} (P : type686 A) (t : type667 A) (f : type639 A) (u : type686 A) : (term557 A P f t u) = (term558 A P t f u).
Proof. exact (MK_COMB (@lem4863132 A u P t f) (@lem4863133 A u)). Qed.
Lemma lem4863135 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term559 A P f u) = (term560 A P f u).
Proof. exact (fun_ext (fun t : type667 A => @lem4863134 A P t f u)). Qed.
Lemma lem4863136 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4863137 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term548 A P f u) = (term561 A P f u).
Proof. exact (MK_COMB (@lem4863136 A) (@lem4863135 A P f u)). Qed.
Lemma lem4863138 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : ((term547 A P f u) = (term548 A P f u)) = ((term544 A P f u) = (term561 A P f u)).
Proof. exact (MK_COMB (@lem4863129 A P f u) (@lem4863137 A P f u)). Qed.
Lemma lem4863139 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term544 A P f u) = (term561 A P f u).
Proof. exact (EQ_MP (@lem4863138 A P f u) (@lem4863119 A P f u)). Qed.
Lemma lem4863140 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term405 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4863115 A P f u) (@lem4863139 A P f u)). Qed.
Lemma lem4863141 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term376 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4862921 A P f u) (@lem4863140 A P f u)). Qed.
Lemma lem4863142 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4862577 A P f u) (@lem4863141 A P f u)). Qed.
Lemma lem4863143 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term561 A P f u.
Proof. exact (EQ_MP (@lem4863142 A P f u) (@lem4862500 A P f u h1)). Qed.
Lemma lem4863153 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term311 A u f s t.
Proof. exact (h1). Qed.
Lemma lem4863159 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term340 A P t) : term340 A P t.
Proof. exact (h1). Qed.
Lemma lem4863160 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term558 A P t' f u.
Proof. exact (h1). Qed.
Lemma lem4863167 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863168 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4863167 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4863169 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4863168 A f s). Qed.
Lemma lem4863170 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4863171 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4863169 A f s) (@lem4863170 A t)). Qed.
Lemma lem4863173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863174 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863173 (A -> Prop) Prop f x). Qed.
Lemma lem4863175 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term562 A f s t).
Proof. exact (@lem4863174 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4863177 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term562 A f s t).
Proof. exact (TRANS (@lem4863171 A f s t) (@lem4863175 A f s t)). Qed.
Lemma lem4863182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863183 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863182 (A -> Prop) Prop f x). Qed.
Lemma lem4863185 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4863183 A u s). Qed.
Lemma lem4863186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863187 {A : Type'} (u : type686 A) (s : A -> Prop) : (term310 A u s) = (term563 A u s).
Proof. exact (MK_COMB (@lem4863186) (@lem4863185 A u s)). Qed.
Lemma lem4863188 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term311 A u f s t) = (term564 A u f s t).
Proof. exact (MK_COMB (@lem4863187 A u s) (@lem4863177 A f s t)). Qed.
Lemma lem4863189 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term564 A u f s t.
Proof. exact (EQ_MP (@lem4863188 A u f s t) (@lem4863153 A u f s t h1)). Qed.
Lemma lem4863190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863195 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863196 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863195 (A -> Prop) Prop f x). Qed.
Lemma lem4863198 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4863196 A P t). Qed.
Lemma lem4863199 {A : Type'} (P : type686 A) (t : A -> Prop) : (term340 A P t) = (term565 A P t).
Proof. exact (MK_COMB (@lem4863190) (@lem4863198 A P t)). Qed.
Lemma lem4863205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863206 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4863205 (type686 A) Prop f x). Qed.
Lemma lem4863208 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@I (((A -> Prop) -> Prop) -> Prop) (@ARBITRARY A) u).
Proof. exact (@lem4863206 A (@ARBITRARY A) u). Qed.
Lemma lem4863213 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863214 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4863213 A Prop f x). Qed.
Lemma lem4863216 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4863214 A c x). Qed.
Lemma lem4863217 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863222 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863223 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4863222 A Prop f x). Qed.
Lemma lem4863225 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4863223 A t x). Qed.
Lemma lem4863226 {A : Type'} (t : A -> Prop) (x : A) : (term355 A t x) = (term566 A t x).
Proof. exact (MK_COMB (@lem4863217) (@lem4863225 A t x)). Qed.
Lemma lem4863227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863234 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863235 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4863234 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4863236 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4863235 A f c). Qed.
Lemma lem4863237 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4863238 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t).
Proof. exact (MK_COMB (@lem4863236 A f c) (@lem4863237 A t)). Qed.
Lemma lem4863240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863241 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863240 (A -> Prop) Prop f x). Qed.
Lemma lem4863242 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t) = (term562 A f c t).
Proof. exact (@lem4863241 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) t). Qed.
Lemma lem4863244 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (term562 A f c t).
Proof. exact (TRANS (@lem4863238 A f c t) (@lem4863242 A f c t)). Qed.
Lemma lem4863245 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term567 A f c t) = (term568 A f c t).
Proof. exact (MK_COMB (@lem4863227) (@lem4863244 A f c t)). Qed.
Lemma lem4863246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863247 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term569 A f c t) = (term570 A f c t).
Proof. exact (MK_COMB (@lem4863246) (@lem4863245 A f c t)). Qed.
Lemma lem4863248 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term345 A f c t x) = (term571 A f c t x).
Proof. exact (MK_COMB (@lem4863247 A f c t) (@lem4863226 A t x)). Qed.
Lemma lem4863249 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term353 A f c x) = (term572 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863248 A f c t x)). Qed.
Lemma lem4863250 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863251 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term354 A f c x) = (term573 A f c x).
Proof. exact (MK_COMB (@lem4863250 A) (@lem4863249 A f c x)). Qed.
Lemma lem4863252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863253 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term357 A f c x) = (term574 A f c x).
Proof. exact (MK_COMB (@lem4863252) (@lem4863251 A f c x)). Qed.
Lemma lem4863254 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term359 A f c x) = (term575 A f c x).
Proof. exact (MK_COMB (@lem4863253 A f c x) (@lem4863216 A c x)). Qed.
Lemma lem4863255 {A : Type'} (f : type639 A) (c : A -> Prop) : (term382 A f c) = (term576 A f c).
Proof. exact (fun_ext (fun x : A => @lem4863254 A f c x)). Qed.
Lemma lem4863256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863257 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term577 A f c).
Proof. exact (MK_COMB (@lem4863256 A) (@lem4863255 A f c)). Qed.
Lemma lem4863258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863264 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4863263 A Prop f x). Qed.
Lemma lem4863266 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4863264 A c x). Qed.
Lemma lem4863267 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term566 A c x).
Proof. exact (MK_COMB (@lem4863258) (@lem4863266 A c x)). Qed.
Lemma lem4863276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863277 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4863276 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4863278 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4863277 A t' c). Qed.
Lemma lem4863279 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4863280 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4863278 A t' c) (@lem4863279 A x)). Qed.
Lemma lem4863282 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863283 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4863282 A (A -> Prop) f x). Qed.
Lemma lem4863284 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term578 A t' c x).
Proof. exact (@lem4863283 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4863285 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term578 A t' c x).
Proof. exact (TRANS (@lem4863280 A t' c x) (@lem4863284 A t' c x)). Qed.
Lemma lem4863286 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4863287 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term579 A t' c x).
Proof. exact (MK_COMB (@lem4863285 A t' c x) (@lem4863286 A x)). Qed.
Lemma lem4863289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863290 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4863289 A Prop f x). Qed.
Lemma lem4863291 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term579 A t' c x) = (term580 A t' c x).
Proof. exact (@lem4863290 A (term578 A t' c x) x). Qed.
Lemma lem4863293 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term580 A t' c x).
Proof. exact (TRANS (@lem4863287 A t' c x) (@lem4863291 A t' c x)). Qed.
Lemma lem4863302 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863303 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4863302 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4863304 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4863303 A t' c). Qed.
Lemma lem4863305 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4863306 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4863304 A t' c) (@lem4863305 A x)). Qed.
Lemma lem4863308 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863309 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4863308 A (A -> Prop) f x). Qed.
Lemma lem4863310 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term578 A t' c x).
Proof. exact (@lem4863309 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4863312 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term578 A t' c x).
Proof. exact (TRANS (@lem4863306 A t' c x) (@lem4863310 A t' c x)). Qed.
Lemma lem4863313 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (f c).
Proof. exact (eq_refl (f c)). Qed.
Lemma lem4863314 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term581 A f t' c x) = (term582 A f t' c x).
Proof. exact (MK_COMB (@lem4863313 A f c) (@lem4863312 A t' c x)). Qed.
Lemma lem4863316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863317 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4863316 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4863318 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4863317 A f c). Qed.
Lemma lem4863319 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term578 A t' c x) = (term578 A t' c x).
Proof. exact (eq_refl (term578 A t' c x)). Qed.
Lemma lem4863320 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term582 A f t' c x) = (term583 A f t' c x).
Proof. exact (MK_COMB (@lem4863318 A f c) (@lem4863319 A t' c x)). Qed.
Lemma lem4863322 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863323 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863322 (A -> Prop) Prop f x). Qed.
Lemma lem4863324 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term583 A f t' c x) = (term584 A f t' c x).
Proof. exact (@lem4863323 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) (term578 A t' c x)). Qed.
Lemma lem4863325 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term582 A f t' c x) = (term584 A f t' c x).
Proof. exact (TRANS (@lem4863320 A f t' c x) (@lem4863324 A f t' c x)). Qed.
Lemma lem4863326 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term581 A f t' c x) = (term584 A f t' c x).
Proof. exact (TRANS (@lem4863314 A f t' c x) (@lem4863325 A f t' c x)). Qed.
Lemma lem4863327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863328 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term585 A f t' c x) = (term586 A f t' c x).
Proof. exact (MK_COMB (@lem4863327) (@lem4863326 A f t' c x)). Qed.
Lemma lem4863329 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term587 A f t' c x) = (term588 A f t' c x).
Proof. exact (MK_COMB (@lem4863328 A f t' c x) (@lem4863293 A t' c x)). Qed.
Lemma lem4863330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863331 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term589 A f t' c x) = (term590 A f t' c x).
Proof. exact (MK_COMB (@lem4863330) (@lem4863329 A f t' c x)). Qed.
Lemma lem4863332 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term591 A f t' c x) = (term592 A f t' c x).
Proof. exact (MK_COMB (@lem4863331 A f t' c x) (@lem4863267 A c x)). Qed.
Lemma lem4863333 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term593 A f t' c) = (term594 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4863332 A f t' c x)). Qed.
Lemma lem4863334 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863335 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term595 A f t' c) = (term596 A f t' c).
Proof. exact (MK_COMB (@lem4863334 A) (@lem4863333 A f t' c)). Qed.
Lemma lem4863336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863337 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term597 A f t' c) = (term598 A f t' c).
Proof. exact (MK_COMB (@lem4863336) (@lem4863335 A f t' c)). Qed.
Lemma lem4863338 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term599 A t' f c) = (term600 A t' f c).
Proof. exact (MK_COMB (@lem4863337 A f t' c) (@lem4863257 A f c)). Qed.
Lemma lem4863343 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863344 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863343 (A -> Prop) Prop f x). Qed.
Lemma lem4863346 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (@I ((A -> Prop) -> Prop) P c').
Proof. exact (@lem4863344 A P c'). Qed.
Lemma lem4863347 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863354 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863355 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4863354 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4863356 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4863355 A f c). Qed.
Lemma lem4863357 {A : Type'} (c' : A -> Prop) : c' = c'.
Proof. exact (eq_refl c'). Qed.
Lemma lem4863358 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c').
Proof. exact (MK_COMB (@lem4863356 A f c) (@lem4863357 A c')). Qed.
Lemma lem4863360 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863361 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863360 (A -> Prop) Prop f x). Qed.
Lemma lem4863362 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c') = (term562 A f c c').
Proof. exact (@lem4863361 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) c'). Qed.
Lemma lem4863364 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (term562 A f c c').
Proof. exact (TRANS (@lem4863358 A f c c') (@lem4863362 A f c c')). Qed.
Lemma lem4863365 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term567 A f c c') = (term568 A f c c').
Proof. exact (MK_COMB (@lem4863347) (@lem4863364 A f c c')). Qed.
Lemma lem4863366 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863367 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term569 A f c c') = (term570 A f c c').
Proof. exact (MK_COMB (@lem4863366) (@lem4863365 A f c c')). Qed.
Lemma lem4863368 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term341 A f c P c') = (term601 A f c P c').
Proof. exact (MK_COMB (@lem4863367 A f c c') (@lem4863346 A P c')). Qed.
Lemma lem4863369 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term342 A f c P) = (term602 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863368 A f c P c')). Qed.
Lemma lem4863370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863371 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term343 A f c P) = (term603 A f c P).
Proof. exact (MK_COMB (@lem4863370 A) (@lem4863369 A f c P)). Qed.
Lemma lem4863372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863373 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term604 A f c P).
Proof. exact (MK_COMB (@lem4863372) (@lem4863371 A f c P)). Qed.
Lemma lem4863374 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term605 A P t' f c) = (term606 A P t' f c).
Proof. exact (MK_COMB (@lem4863373 A f c P) (@lem4863338 A t' f c)). Qed.
Lemma lem4863375 {A : Type'} : (@ARBITRARY A) = (@ARBITRARY A).
Proof. exact (eq_refl (@ARBITRARY A)). Qed.
Lemma lem4863380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863381 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4863380 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4863383 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4863381 A f c). Qed.
Lemma lem4863384 {A : Type'} (f : type639 A) (c : A -> Prop) : (term490 A f c) = (term607 A f c).
Proof. exact (MK_COMB (@lem4863375 A) (@lem4863383 A f c)). Qed.
Lemma lem4863386 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863387 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4863386 (type686 A) Prop f x). Qed.
Lemma lem4863388 {A : Type'} (f : type639 A) (c : A -> Prop) : (term607 A f c) = (term608 A f c).
Proof. exact (@lem4863387 A (@ARBITRARY A) (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c)). Qed.
Lemma lem4863389 {A : Type'} (f : type639 A) (c : A -> Prop) : (term490 A f c) = (term608 A f c).
Proof. exact (TRANS (@lem4863384 A f c) (@lem4863388 A f c)). Qed.
Lemma lem4863390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863391 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term609 A f c).
Proof. exact (MK_COMB (@lem4863390) (@lem4863389 A f c)). Qed.
Lemma lem4863392 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term610 A P t' f c) = (term611 A P t' f c).
Proof. exact (MK_COMB (@lem4863391 A f c) (@lem4863374 A P t' f c)). Qed.
Lemma lem4863393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4863398 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4863399 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4863398 (A -> Prop) Prop f x). Qed.
Lemma lem4863401 {A : Type'} (u : type686 A) (c : A -> Prop) : (u c) = (@I ((A -> Prop) -> Prop) u c).
Proof. exact (@lem4863399 A u c). Qed.
Lemma lem4863402 {A : Type'} (u : type686 A) (c : A -> Prop) : (term340 A u c) = (term565 A u c).
Proof. exact (MK_COMB (@lem4863393) (@lem4863401 A u c)). Qed.
Lemma lem4863403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863404 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term612 A u c).
Proof. exact (MK_COMB (@lem4863403) (@lem4863402 A u c)). Qed.
Lemma lem4863405 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term535 A u P t' f c) = (term613 A u P t' f c).
Proof. exact (MK_COMB (@lem4863404 A u c) (@lem4863392 A P t' f c)). Qed.
Lemma lem4863406 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term537 A u P t' f) = (term614 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863405 A u P t' f c)). Qed.
Lemma lem4863407 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863408 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term539 A u P t' f) = (term615 A u P t' f).
Proof. exact (MK_COMB (@lem4863407 A) (@lem4863406 A u P t' f)). Qed.
Lemma lem4863409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863410 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term556 A u P t' f) = (term616 A u P t' f).
Proof. exact (MK_COMB (@lem4863409) (@lem4863408 A u P t' f)). Qed.
Lemma lem4863411 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) : (term558 A P t' f u) = (term617 A P t' f u).
Proof. exact (MK_COMB (@lem4863410 A u P t' f) (@lem4863208 A u)). Qed.
Lemma lem4863412 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term617 A P t' f u.
Proof. exact (EQ_MP (@lem4863411 A P t' f u) (@lem4863160 A P t' f u h1)). Qed.
Lemma lem4863414 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term615 A u P t' f.
Proof. exact (proj1 (@lem4863412 A P t' f u h1)). Qed.
Lemma lem4863422 {A : Type'} (P : A -> Prop) (Q : Prop) : (term618 A P Q) = (term619 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4863423 {A : Type'} (P : type686 A) (Q : Prop) : (term620 A P Q) = (term621 A P Q).
Proof. exact (@lem4863422 (A -> Prop) P Q). Qed.
Lemma lem4863424 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term623 A f c x).
Proof. exact (@lem4863423 A (term572 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4863425 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4863426 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term625 A f c x) = (term572 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863425 A f c t x)). Qed.
Lemma lem4863427 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863428 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term626 A f c x) = (term573 A f c x).
Proof. exact (MK_COMB (@lem4863427 A) (@lem4863426 A f c x)). Qed.
Lemma lem4863429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863430 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term627 A f c x) = (term574 A f c x).
Proof. exact (MK_COMB (@lem4863429) (@lem4863428 A f c x)). Qed.
Lemma lem4863431 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4863432 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term575 A f c x).
Proof. exact (MK_COMB (@lem4863430 A f c x) (@lem4863431 A c x)). Qed.
Lemma lem4863433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863434 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term628 A f c x) = (term629 A f c x).
Proof. exact (MK_COMB (@lem4863433) (@lem4863432 A f c x)). Qed.
Lemma lem4863435 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4863436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4863437 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term630 A f c x t) = (term631 A f c t x).
Proof. exact (MK_COMB (@lem4863436) (@lem4863435 A f c t x)). Qed.
Lemma lem4863438 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4863439 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term632 A f t c x) = (term633 A f t c x).
Proof. exact (MK_COMB (@lem4863437 A f c t x) (@lem4863438 A c x)). Qed.
Lemma lem4863440 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term634 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863439 A f t c x)). Qed.
Lemma lem4863441 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863442 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term623 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4863441 A) (@lem4863440 A f c x)). Qed.
Lemma lem4863443 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term622 A f c x) = (term623 A f c x)) = ((term575 A f c x) = (term636 A f c x)).
Proof. exact (MK_COMB (@lem4863434 A f c x) (@lem4863442 A f c x)). Qed.
Lemma lem4863444 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term575 A f c x) = (term636 A f c x).
Proof. exact (EQ_MP (@lem4863443 A f c x) (@lem4863424 A f c x)). Qed.
Lemma lem4863445 {A : Type'} (f : type639 A) (c : A -> Prop) : (term576 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4863444 A f c x)). Qed.
Lemma lem4863446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863447 {A : Type'} (f : type639 A) (c : A -> Prop) : (term577 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4863446 A) (@lem4863445 A f c)). Qed.
Lemma lem4863448 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term598 A f t' c) = (term598 A f t' c).
Proof. exact (eq_refl (term598 A f t' c)). Qed.
Lemma lem4863449 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4863448 A f t' c) (@lem4863447 A f c)). Qed.
Lemma lem4863451 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4863452 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (@lem4863451 A P Q). Qed.
Lemma lem4863453 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term641 A t' f c).
Proof. exact (@lem4863452 A (term594 A f t' c) (term637 A f c)). Qed.
Lemma lem4863454 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4863455 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term643 A f t' c) = (term594 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4863454 A f t' c x)). Qed.
Lemma lem4863456 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863457 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term644 A f t' c) = (term596 A f t' c).
Proof. exact (MK_COMB (@lem4863456 A) (@lem4863455 A f t' c)). Qed.
Lemma lem4863458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863459 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term645 A f t' c) = (term598 A f t' c).
Proof. exact (MK_COMB (@lem4863458) (@lem4863457 A f t' c)). Qed.
Lemma lem4863460 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4863461 {A : Type'} (f : type639 A) (c : A -> Prop) : (term647 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4863460 A f c x)). Qed.
Lemma lem4863462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863463 {A : Type'} (f : type639 A) (c : A -> Prop) : (term648 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4863462 A) (@lem4863461 A f c)). Qed.
Lemma lem4863464 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4863459 A f t' c) (@lem4863463 A f c)). Qed.
Lemma lem4863465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863466 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term649 A t' f c) = (term650 A t' f c).
Proof. exact (MK_COMB (@lem4863465) (@lem4863464 A t' f c)). Qed.
Lemma lem4863467 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4863468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863469 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term651 A f t' c x) = (term652 A f t' c x).
Proof. exact (MK_COMB (@lem4863468) (@lem4863467 A f t' c x)). Qed.
Lemma lem4863470 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4863471 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term653 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4863469 A f t' c x) (@lem4863470 A f c x)). Qed.
Lemma lem4863472 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term655 A t' f c) = (term656 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863471 A t' f c x)). Qed.
Lemma lem4863473 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863474 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term641 A t' f c) = (term657 A t' f c).
Proof. exact (MK_COMB (@lem4863473 A) (@lem4863472 A t' f c)). Qed.
Lemma lem4863475 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term640 A t' f c) = (term641 A t' f c)) = ((term639 A t' f c) = (term657 A t' f c)).
Proof. exact (MK_COMB (@lem4863466 A t' f c) (@lem4863474 A t' f c)). Qed.
Lemma lem4863476 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term657 A t' f c).
Proof. exact (EQ_MP (@lem4863475 A t' f c) (@lem4863453 A t' f c)). Qed.
Lemma lem4863478 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863479 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4863478 (A -> Prop) P Q). Qed.
Lemma lem4863480 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term663 A t' f c x).
Proof. exact (@lem4863479 A (term592 A f t' c x) (term635 A f c x)). Qed.
Lemma lem4863481 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4863482 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863481 A f t c x)). Qed.
Lemma lem4863483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863484 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4863483 A) (@lem4863482 A f c x)). Qed.
Lemma lem4863485 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4863486 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4863485 A f t' c x) (@lem4863484 A f c x)). Qed.
Lemma lem4863487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863488 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term667 A t' f c x) = (term668 A t' f c x).
Proof. exact (MK_COMB (@lem4863487) (@lem4863486 A t' f c x)). Qed.
Lemma lem4863489 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4863490 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4863491 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term669 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (MK_COMB (@lem4863490 A f t' c x) (@lem4863489 A f t c x)). Qed.
Lemma lem4863492 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term671 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863491 A t' f t c x)). Qed.
Lemma lem4863493 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863494 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term663 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4863493 A) (@lem4863492 A t' f c x)). Qed.
Lemma lem4863495 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A t' f c x) = (term663 A t' f c x)) = ((term654 A t' f c x) = (term673 A t' f c x)).
Proof. exact (MK_COMB (@lem4863488 A t' f c x) (@lem4863494 A t' f c x)). Qed.
Lemma lem4863496 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term654 A t' f c x) = (term673 A t' f c x).
Proof. exact (EQ_MP (@lem4863495 A t' f c x) (@lem4863480 A t' f c x)). Qed.
Lemma lem4863497 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term656 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863496 A t' f c x)). Qed.
Lemma lem4863498 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863499 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term657 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4863498 A) (@lem4863497 A t' f c)). Qed.
Lemma lem4863500 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4863476 A t' f c) (@lem4863499 A t' f c)). Qed.
Lemma lem4863501 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4863449 A t' f c) (@lem4863500 A t' f c)). Qed.
Lemma lem4863502 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term604 A f c P) = (term604 A f c P).
Proof. exact (eq_refl (term604 A f c P)). Qed.
Lemma lem4863503 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4863502 A f c P) (@lem4863501 A t' f c)). Qed.
Lemma lem4863507 {A : Type'} (P : A -> Prop) (Q : Prop) : (term677 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4863508 {A : Type'} (P : type686 A) (Q : Prop) : (term679 A P Q) = (term680 A P Q).
Proof. exact (@lem4863507 (A -> Prop) P Q). Qed.
Lemma lem4863509 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term682 A P t' f c).
Proof. exact (@lem4863508 A (term602 A f c P) (term675 A t' f c)). Qed.
Lemma lem4863510 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4863511 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term684 A f c P) = (term602 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863510 A f c P c')). Qed.
Lemma lem4863512 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863513 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term685 A f c P) = (term603 A f c P).
Proof. exact (MK_COMB (@lem4863512 A) (@lem4863511 A f c P)). Qed.
Lemma lem4863514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863515 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term686 A f c P) = (term604 A f c P).
Proof. exact (MK_COMB (@lem4863514) (@lem4863513 A f c P)). Qed.
Lemma lem4863516 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4863517 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4863515 A f c P) (@lem4863516 A t' f c)). Qed.
Lemma lem4863518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863519 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term687 A P t' f c) = (term688 A P t' f c).
Proof. exact (MK_COMB (@lem4863518) (@lem4863517 A P t' f c)). Qed.
Lemma lem4863520 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4863521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863522 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term689 A f c P c') = (term690 A f c P c').
Proof. exact (MK_COMB (@lem4863521) (@lem4863520 A f c P c')). Qed.
Lemma lem4863523 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4863524 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term691 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863522 A f c P c') (@lem4863523 A t' f c)). Qed.
Lemma lem4863525 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term693 A P t' f c) = (term694 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863524 A P c' t' f c)). Qed.
Lemma lem4863526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863527 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term682 A P t' f c) = (term695 A P t' f c).
Proof. exact (MK_COMB (@lem4863526 A) (@lem4863525 A P t' f c)). Qed.
Lemma lem4863528 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term681 A P t' f c) = (term682 A P t' f c)) = ((term676 A P t' f c) = (term695 A P t' f c)).
Proof. exact (MK_COMB (@lem4863519 A P t' f c) (@lem4863527 A P t' f c)). Qed.
Lemma lem4863529 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term695 A P t' f c).
Proof. exact (EQ_MP (@lem4863528 A P t' f c) (@lem4863509 A P t' f c)). Qed.
Lemma lem4863531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863532 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4863531 A P Q). Qed.
Lemma lem4863533 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term697 A P c' t' f c).
Proof. exact (@lem4863532 A (term601 A f c P c') (term674 A t' f c)). Qed.
Lemma lem4863534 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4863535 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term699 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863534 A t' f c x)). Qed.
Lemma lem4863536 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863537 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term700 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4863536 A) (@lem4863535 A t' f c)). Qed.
Lemma lem4863538 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4863539 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863538 A f c P c') (@lem4863537 A t' f c)). Qed.
Lemma lem4863540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863541 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term701 A P c' t' f c) = (term702 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863540) (@lem4863539 A P c' t' f c)). Qed.
Lemma lem4863542 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4863543 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4863544 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863543 A f c P c') (@lem4863542 A t' f c x)). Qed.
Lemma lem4863545 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term705 A P c' t' f c) = (term706 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863544 A P c' t' f c x)). Qed.
Lemma lem4863546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863547 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863546 A) (@lem4863545 A P c' t' f c)). Qed.
Lemma lem4863548 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term696 A P c' t' f c) = (term697 A P c' t' f c)) = ((term692 A P c' t' f c) = (term707 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4863541 A P c' t' f c) (@lem4863547 A P c' t' f c)). Qed.
Lemma lem4863549 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (EQ_MP (@lem4863548 A P c' t' f c) (@lem4863533 A P c' t' f c)). Qed.
Lemma lem4863551 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863552 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4863551 (A -> Prop) P Q). Qed.
Lemma lem4863553 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term709 A P c' t' f c x).
Proof. exact (@lem4863552 A (term601 A f c P c') (term672 A t' f c x)). Qed.
Lemma lem4863554 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4863555 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863554 A t' f t c x)). Qed.
Lemma lem4863556 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863557 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term712 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4863556 A) (@lem4863555 A t' f c x)). Qed.
Lemma lem4863558 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4863559 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863558 A f c P c') (@lem4863557 A t' f c x)). Qed.
Lemma lem4863560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863561 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term713 A P c' t' f c x) = (term714 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863560) (@lem4863559 A P c' t' f c x)). Qed.
Lemma lem4863562 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4863563 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4863564 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term715 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863563 A f c P c') (@lem4863562 A t' f t c x)). Qed.
Lemma lem4863565 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term717 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863564 A P c' t' f t c x)). Qed.
Lemma lem4863566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863567 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term709 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863566 A) (@lem4863565 A P c' t' f c x)). Qed.
Lemma lem4863568 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term708 A P c' t' f c x) = (term709 A P c' t' f c x)) = ((term704 A P c' t' f c x) = (term719 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4863561 A P c' t' f c x) (@lem4863567 A P c' t' f c x)). Qed.
Lemma lem4863569 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term704 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4863568 A P c' t' f c x) (@lem4863553 A P c' t' f c x)). Qed.
Lemma lem4863570 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term706 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863569 A P c' t' f c x)). Qed.
Lemma lem4863571 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863572 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term707 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863571 A) (@lem4863570 A P c' t' f c)). Qed.
Lemma lem4863573 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (TRANS (@lem4863549 A P c' t' f c) (@lem4863572 A P c' t' f c)). Qed.
Lemma lem4863574 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term694 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863573 A P c' t' f c)). Qed.
Lemma lem4863575 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863576 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4863575 A) (@lem4863574 A P t' f c)). Qed.
Lemma lem4863577 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4863529 A P t' f c) (@lem4863576 A P t' f c)). Qed.
Lemma lem4863578 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4863503 A P t' f c) (@lem4863577 A P t' f c)). Qed.
Lemma lem4863579 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863580 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4863579 A f c) (@lem4863578 A P t' f c)). Qed.
Lemma lem4863582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863583 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4863582 (A -> Prop) P Q). Qed.
Lemma lem4863584 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term726 A P t' f c).
Proof. exact (@lem4863583 A (term608 A f c) (term722 A P t' f c)). Qed.
Lemma lem4863585 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4863586 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term728 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863585 A P c' t' f c)). Qed.
Lemma lem4863587 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863588 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term729 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4863587 A) (@lem4863586 A P t' f c)). Qed.
Lemma lem4863589 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863590 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4863589 A f c) (@lem4863588 A P t' f c)). Qed.
Lemma lem4863591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863592 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term730 A P t' f c) = (term731 A P t' f c).
Proof. exact (MK_COMB (@lem4863591) (@lem4863590 A P t' f c)). Qed.
Lemma lem4863593 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4863594 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863595 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P t' f c c') = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863594 A f c) (@lem4863593 A P c' t' f c)). Qed.
Lemma lem4863596 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term735 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863595 A P c' t' f c)). Qed.
Lemma lem4863597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863598 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term726 A P t' f c) = (term736 A P t' f c).
Proof. exact (MK_COMB (@lem4863597 A) (@lem4863596 A P t' f c)). Qed.
Lemma lem4863599 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term725 A P t' f c) = (term726 A P t' f c)) = ((term724 A P t' f c) = (term736 A P t' f c)).
Proof. exact (MK_COMB (@lem4863592 A P t' f c) (@lem4863598 A P t' f c)). Qed.
Lemma lem4863600 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term736 A P t' f c).
Proof. exact (EQ_MP (@lem4863599 A P t' f c) (@lem4863584 A P t' f c)). Qed.
Lemma lem4863602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863603 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4863602 A P Q). Qed.
Lemma lem4863604 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term738 A P c' t' f c).
Proof. exact (@lem4863603 A (term608 A f c) (term720 A P c' t' f c)). Qed.
Lemma lem4863605 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4863606 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863605 A P c' t' f c x)). Qed.
Lemma lem4863607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863608 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863607 A) (@lem4863606 A P c' t' f c)). Qed.
Lemma lem4863609 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863610 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863609 A f c) (@lem4863608 A P c' t' f c)). Qed.
Lemma lem4863611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863612 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term742 A P c' t' f c) = (term743 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863611) (@lem4863610 A P c' t' f c)). Qed.
Lemma lem4863613 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4863614 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863615 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863614 A f c) (@lem4863613 A P c' t' f c x)). Qed.
Lemma lem4863616 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863615 A P c' t' f c x)). Qed.
Lemma lem4863617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863618 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term738 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863617 A) (@lem4863616 A P c' t' f c)). Qed.
Lemma lem4863619 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term737 A P c' t' f c) = (term738 A P c' t' f c)) = ((term733 A P c' t' f c) = (term748 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4863612 A P c' t' f c) (@lem4863618 A P c' t' f c)). Qed.
Lemma lem4863620 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (EQ_MP (@lem4863619 A P c' t' f c) (@lem4863604 A P c' t' f c)). Qed.
Lemma lem4863622 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4863623 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4863622 (A -> Prop) P Q). Qed.
Lemma lem4863624 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term750 A P c' t' f c x).
Proof. exact (@lem4863623 A (term608 A f c) (term718 A P c' t' f c x)). Qed.
Lemma lem4863625 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4863626 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863625 A P c' t' f t c x)). Qed.
Lemma lem4863627 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863628 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863627 A) (@lem4863626 A P c' t' f c x)). Qed.
Lemma lem4863629 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863630 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863629 A f c) (@lem4863628 A P c' t' f c x)). Qed.
Lemma lem4863631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863632 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term754 A P c' t' f c x) = (term755 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863631) (@lem4863630 A P c' t' f c x)). Qed.
Lemma lem4863633 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4863634 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863635 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863634 A f c) (@lem4863633 A P c' t' f t c x)). Qed.
Lemma lem4863636 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term758 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863635 A P c' t' f t c x)). Qed.
Lemma lem4863637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863638 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term750 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863637 A) (@lem4863636 A P c' t' f c x)). Qed.
Lemma lem4863639 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term749 A P c' t' f c x) = (term750 A P c' t' f c x)) = ((term745 A P c' t' f c x) = (term760 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4863632 A P c' t' f c x) (@lem4863638 A P c' t' f c x)). Qed.
Lemma lem4863640 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term745 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4863639 A P c' t' f c x) (@lem4863624 A P c' t' f c x)). Qed.
Lemma lem4863641 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863640 A P c' t' f c x)). Qed.
Lemma lem4863642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863643 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term748 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863642 A) (@lem4863641 A P c' t' f c)). Qed.
Lemma lem4863644 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (TRANS (@lem4863620 A P c' t' f c) (@lem4863643 A P c' t' f c)). Qed.
Lemma lem4863645 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863644 A P c' t' f c)). Qed.
Lemma lem4863646 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863647 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4863646 A) (@lem4863645 A P t' f c)). Qed.
Lemma lem4863648 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4863600 A P t' f c) (@lem4863647 A P t' f c)). Qed.
Lemma lem4863649 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4863580 A P t' f c) (@lem4863648 A P t' f c)). Qed.
Lemma lem4863650 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863651 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4863650 A u c) (@lem4863649 A P t' f c)). Qed.
Lemma lem4863653 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4863654 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4863653 (A -> Prop) P Q). Qed.
Lemma lem4863655 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term771 A u P t' f c).
Proof. exact (@lem4863654 A (term565 A u c) (term763 A P t' f c)). Qed.
Lemma lem4863656 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4863657 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863656 A P c' t' f c)). Qed.
Lemma lem4863658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863659 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4863658 A) (@lem4863657 A P t' f c)). Qed.
Lemma lem4863660 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863661 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4863660 A u c) (@lem4863659 A P t' f c)). Qed.
Lemma lem4863662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863663 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A u P t' f c) = (term776 A u P t' f c).
Proof. exact (MK_COMB (@lem4863662) (@lem4863661 A u P t' f c)). Qed.
Lemma lem4863664 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4863665 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863666 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A u P t' f c c') = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4863665 A u c) (@lem4863664 A P c' t' f c)). Qed.
Lemma lem4863667 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term779 A u P t' f c) = (term780 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863666 A u P c' t' f c)). Qed.
Lemma lem4863668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863669 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term771 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (MK_COMB (@lem4863668 A) (@lem4863667 A u P t' f c)). Qed.
Lemma lem4863670 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term770 A u P t' f c) = (term771 A u P t' f c)) = ((term765 A u P t' f c) = (term781 A u P t' f c)).
Proof. exact (MK_COMB (@lem4863663 A u P t' f c) (@lem4863669 A u P t' f c)). Qed.
Lemma lem4863671 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (EQ_MP (@lem4863670 A u P t' f c) (@lem4863655 A u P t' f c)). Qed.
Lemma lem4863673 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4863674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (@lem4863673 A P Q). Qed.
Lemma lem4863675 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term783 A u P c' t' f c).
Proof. exact (@lem4863674 A (term565 A u c) (term761 A P c' t' f c)). Qed.
Lemma lem4863676 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4863677 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term785 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863676 A P c' t' f c x)). Qed.
Lemma lem4863678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863679 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4863678 A) (@lem4863677 A P c' t' f c)). Qed.
Lemma lem4863680 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863681 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4863680 A u c) (@lem4863679 A P c' t' f c)). Qed.
Lemma lem4863682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863683 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A u P c' t' f c) = (term788 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4863682) (@lem4863681 A u P c' t' f c)). Qed.
Lemma lem4863684 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4863685 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863686 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4863685 A u c) (@lem4863684 A P c' t' f c x)). Qed.
Lemma lem4863687 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term791 A u P c' t' f c) = (term792 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863686 A u P c' t' f c x)). Qed.
Lemma lem4863688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863689 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term783 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4863688 A) (@lem4863687 A u P c' t' f c)). Qed.
Lemma lem4863690 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term782 A u P c' t' f c) = (term783 A u P c' t' f c)) = ((term778 A u P c' t' f c) = (term793 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4863683 A u P c' t' f c) (@lem4863689 A u P c' t' f c)). Qed.
Lemma lem4863691 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4863690 A u P c' t' f c) (@lem4863675 A u P c' t' f c)). Qed.
Lemma lem4863693 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4863694 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4863693 (A -> Prop) P Q). Qed.
Lemma lem4863695 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term795 A u P c' t' f c x).
Proof. exact (@lem4863694 A (term565 A u c) (term759 A P c' t' f c x)). Qed.
Lemma lem4863696 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4863697 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term797 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863696 A P c' t' f t c x)). Qed.
Lemma lem4863698 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863699 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4863698 A) (@lem4863697 A P c' t' f c x)). Qed.
Lemma lem4863700 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863701 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4863700 A u c) (@lem4863699 A P c' t' f c x)). Qed.
Lemma lem4863702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863703 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term799 A u P c' t' f c x) = (term800 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4863702) (@lem4863701 A u P c' t' f c x)). Qed.
Lemma lem4863704 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4863705 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863706 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term801 A u P c' t' f c x t) = (term802 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863705 A u c) (@lem4863704 A P c' t' f t c x)). Qed.
Lemma lem4863707 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term803 A u P c' t' f c x) = (term804 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863706 A u P c' t' f t c x)). Qed.
Lemma lem4863708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863709 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term795 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4863708 A) (@lem4863707 A u P c' t' f c x)). Qed.
Lemma lem4863710 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term794 A u P c' t' f c x) = (term795 A u P c' t' f c x)) = ((term790 A u P c' t' f c x) = (term805 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4863703 A u P c' t' f c x) (@lem4863709 A u P c' t' f c x)). Qed.
Lemma lem4863711 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4863710 A u P c' t' f c x) (@lem4863695 A u P c' t' f c x)). Qed.
Lemma lem4863712 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term792 A u P c' t' f c) = (term806 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4863711 A u P c' t' f c x)). Qed.
Lemma lem4863713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863714 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term793 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4863713 A) (@lem4863712 A u P c' t' f c)). Qed.
Lemma lem4863715 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (TRANS (@lem4863691 A u P c' t' f c) (@lem4863714 A u P c' t' f c)). Qed.
Lemma lem4863716 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A u P t' f c) = (term808 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863715 A u P c' t' f c)). Qed.
Lemma lem4863717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863718 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (MK_COMB (@lem4863717 A) (@lem4863716 A u P t' f c)). Qed.
Lemma lem4863719 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4863671 A u P t' f c) (@lem4863718 A u P t' f c)). Qed.
Lemma lem4863720 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4863651 A u P t' f c) (@lem4863719 A u P t' f c)). Qed.
Lemma lem4863721 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term614 A u P t' f) = (term810 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863720 A u P t' f c)). Qed.
Lemma lem4863722 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863723 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term615 A u P t' f) = (term811 A u P t' f).
Proof. exact (MK_COMB (@lem4863722 A) (@lem4863721 A u P t' f)). Qed.
Lemma lem4863736 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term633 A f t c x) = (term633 A f t c x).
Proof. exact (eq_refl (term633 A f t c x)). Qed.
Lemma lem4863753 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term592 A f t' c x) = (term812 A f t' c x).
Proof. exact (@lem19699 (term584 A f t' c x) (term580 A t' c x) (term566 A c x)). Qed.
Lemma lem4863754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863755 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term813 A f t' c x).
Proof. exact (MK_COMB (@lem4863754) (@lem4863753 A f t' c x)). Qed.
Lemma lem4863756 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term670 A t' f t c x) = (term814 A t' f t c x).
Proof. exact (MK_COMB (@lem4863755 A f t' c x) (@lem4863736 A f t c x)). Qed.
Lemma lem4863765 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4863766 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term716 A P c' t' f t c x) = (term815 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863765 A f c P c') (@lem4863756 A t' f t c x)). Qed.
Lemma lem4863769 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4863770 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term757 A P c' t' f t c x) = (term816 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863769 A f c) (@lem4863766 A P c' t' f t c x)). Qed.
Lemma lem4863773 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4863774 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term817 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4863773 A u c) (@lem4863770 A P c' t' f t c x)). Qed.
Lemma lem4863775 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term818 A u P c' t' f t c x).
Proof. exact (@lem19490 (term608 A f c) (term565 A u c) (term815 A P c' t' f t c x)). Qed.
Lemma lem4863776 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term820 A P c' u t' f t c x).
Proof. exact (@lem19490 (term601 A f c P c') (term565 A u c) (term814 A t' f t c x)). Qed.
Lemma lem4863777 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term822 A t' u f t c x).
Proof. exact (@lem19490 (term812 A f t' c x) (term565 A u c) (term633 A f t c x)). Qed.
Lemma lem4863778 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term823 A u f t c x) = (term823 A u f t c x).
Proof. exact (eq_refl (term823 A u f t c x)). Qed.
Lemma lem4863785 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term824 A u f t' c x) = (term825 A f u t' c x).
Proof. exact (@lem19490 (term826 A f t' c x) (term565 A u c) (term827 A t' c x)). Qed.
Lemma lem4863786 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4863787 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term828 A u f t' c x) = (term829 A f u t' c x).
Proof. exact (MK_COMB (@lem4863786) (@lem4863785 A f u t' c x)). Qed.
Lemma lem4863788 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term822 A t' u f t c x) = (term830 A t' u f t c x).
Proof. exact (MK_COMB (@lem4863787 A f u t' c x) (@lem4863778 A u f t c x)). Qed.
Lemma lem4863789 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term830 A t' u f t c x).
Proof. exact (TRANS (@lem4863777 A t' u f t c x) (@lem4863788 A t' u f t c x)). Qed.
Lemma lem4863792 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term831 A u f c P c') = (term831 A u f c P c').
Proof. exact (eq_refl (term831 A u f c P c')). Qed.
Lemma lem4863793 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term820 A P c' u t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4863792 A u f c P c') (@lem4863789 A t' u f t c x)). Qed.
Lemma lem4863794 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4863776 A P c' u t' f t c x) (@lem4863793 A P c' t' u f t c x)). Qed.
Lemma lem4863797 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term833 A u f c) = (term833 A u f c).
Proof. exact (eq_refl (term833 A u f c)). Qed.
Lemma lem4863798 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term818 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4863797 A u f c) (@lem4863794 A P c' t' u f t c x)). Qed.
Lemma lem4863799 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4863775 A u P c' t' f t c x) (@lem4863798 A P c' t' u f t c x)). Qed.
Lemma lem4863800 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4863774 A u P c' t' f t c x) (@lem4863799 A P c' t' u f t c x)). Qed.
Lemma lem4863801 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term804 A u P c' t' f c x) = (term835 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4863800 A P c' t' u f t c x)). Qed.
Lemma lem4863802 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863803 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term805 A u P c' t' f c x) = (term836 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4863802 A) (@lem4863801 A P c' t' u f c x)). Qed.
Lemma lem4863804 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term806 A u P c' t' f c) = (term837 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4863803 A P c' t' u f c x)). Qed.
Lemma lem4863805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4863806 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term807 A u P c' t' f c) = (term838 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4863805 A) (@lem4863804 A P c' t' u f c)). Qed.
Lemma lem4863807 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term808 A u P t' f c) = (term839 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4863806 A P c' t' u f c)). Qed.
Lemma lem4863808 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863809 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term809 A u P t' f c) = (term840 A P t' u f c).
Proof. exact (MK_COMB (@lem4863808 A) (@lem4863807 A P t' u f c)). Qed.
Lemma lem4863810 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term810 A u P t' f) = (term841 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4863809 A P t' u f c)). Qed.
Lemma lem4863811 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4863812 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term811 A u P t' f) = (term842 A P t' u f).
Proof. exact (MK_COMB (@lem4863811 A) (@lem4863810 A P t' u f)). Qed.
Lemma lem4863813 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term615 A u P t' f) = (term842 A P t' u f).
Proof. exact (TRANS (@lem4863723 A u P t' f) (@lem4863812 A P t' u f)). Qed.
Lemma lem4863814 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term842 A P t' u f.
Proof. exact (EQ_MP (@lem4863813 A P t' u f) (@lem4863414 A P t' f u h1)). Qed.
Lemma lem4863827 {A : Type'} (_60240 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term843 A P t' u f _60240.
Proof. exact (@lem4863814 A P t' f u h1 _60240). Qed.
Lemma lem4863828 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) : (term843 A P t' u f _60240) = (term840 A P t' u f _60240).
Proof. exact (eq_refl (term843 A P t' u f _60240)). Qed.
Lemma lem4863829 {A : Type'} (_60240 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term840 A P t' u f _60240.
Proof. exact (EQ_MP (@lem4863828 A P t' u f _60240) (@lem4863827 A _60240 P t' f u h1)). Qed.
Lemma lem4863830 {A : Type'} (_60240 : A -> Prop) (_60241 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term844 A P t' u f _60240 _60241.
Proof. exact (@lem4863829 A _60240 P t' f u h1 _60241). Qed.
Lemma lem4863831 {A : Type'} (P : type686 A) (_60241 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) : (term844 A P t' u f _60240 _60241) = (term838 A P _60241 t' u f _60240).
Proof. exact (eq_refl (term844 A P t' u f _60240 _60241)). Qed.
Lemma lem4863832 {A : Type'} (_60241 : A -> Prop) (_60240 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term838 A P _60241 t' u f _60240.
Proof. exact (EQ_MP (@lem4863831 A P _60241 t' u f _60240) (@lem4863830 A _60240 _60241 P t' f u h1)). Qed.
Lemma lem4863833 {A : Type'} (_60241 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term845 A P _60241 t' u f _60240 _60242.
Proof. exact (@lem4863832 A _60241 _60240 P t' f u h1 _60242). Qed.
Lemma lem4863834 {A : Type'} (P : type686 A) (_60241 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60242 : A) : (term845 A P _60241 t' u f _60240 _60242) = (term836 A P _60241 t' u f _60240 _60242).
Proof. exact (eq_refl (term845 A P _60241 t' u f _60240 _60242)). Qed.
Lemma lem4863835 {A : Type'} (_60241 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term836 A P _60241 t' u f _60240 _60242.
Proof. exact (EQ_MP (@lem4863834 A P _60241 t' u f _60240 _60242) (@lem4863833 A _60241 _60240 _60242 P t' f u h1)). Qed.
Lemma lem4863836 {A : Type'} (_60241 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) (_60243 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term846 A P _60241 t' u f _60240 _60242 _60243.
Proof. exact (@lem4863835 A _60241 _60240 _60242 P t' f u h1 _60243). Qed.
Lemma lem4863837 {A : Type'} (P : type686 A) (_60241 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60243 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) : (term846 A P _60241 t' u f _60240 _60242 _60243) = (term834 A P _60241 t' u f _60243 _60240 _60242).
Proof. exact (eq_refl (term846 A P _60241 t' u f _60240 _60242 _60243)). Qed.
Lemma lem4863838 {A : Type'} (_60241 : A -> Prop) (_60243 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term834 A P _60241 t' u f _60243 _60240 _60242.
Proof. exact (EQ_MP (@lem4863837 A P _60241 t' u f _60243 _60240 _60242) (@lem4863836 A _60241 _60240 _60242 _60243 P t' f u h1)). Qed.
Lemma lem4863839 {A : Type'} (_60241 : A -> Prop) (_60243 : A -> Prop) (_60240 : A -> Prop) (_60242 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term832 A P _60241 t' u f _60243 _60240 _60242.
Proof. exact (proj2 (@lem4863838 A _60241 _60243 _60240 _60242 P t' f u h1)). Qed.
Lemma lem4863848 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term340 A P t) : term565 A P t.
Proof. exact (EQ_MP (@lem4863199 A P t) (@lem4863159 A P t h1)). Qed.
Lemma lem4863870 {A : Type'} (_60240 : A -> Prop) (_60241 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term847 A u f _60240 P _60241.
Proof. exact (proj1 (@lem4863839 A _60241 (@el (A -> Prop)) _60240 (@el A) P t' f u h1)). Qed.
Lemma lem4863908 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4863189 A u f s t h1)). Qed.
Lemma lem4863909 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4863908 A u f s t h1). Qed.
Lemma lem4863911 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4863912 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4863911 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4863913 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4863912 A u s) (@lem4863909 A u f s t h1)). Qed.
Lemma lem4863915 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term562 A f s t.
Proof. exact (proj2 (@lem4863189 A u f s t h1)). Qed.
Lemma lem4863916 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term850 A f s t.
Proof. exact (fun h0 : term568 A f s t => @lem4863915 A u f s t h1). Qed.
Lemma lem4863918 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4863919 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term850 A f s t) = (term562 A f s t).
Proof. exact (@lem4863918 (term562 A f s t)). Qed.
Lemma lem4863920 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term562 A f s t.
Proof. exact (EQ_MP (@lem4863919 A f s t) (@lem4863916 A u f s t h1)). Qed.
Lemma lem4863936 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4863937 {A : Type'} (P : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term601 A f _60240 P _60241) = (term851 A P f _60240 _60241).
Proof. exact (@lem4863936 (@I ((A -> Prop) -> Prop) P _60241) (term568 A f _60240 _60241)). Qed.
Lemma lem4863943 {A : Type'} (u : type686 A) (_60240 : A -> Prop) : (term612 A u _60240) = (term612 A u _60240).
Proof. exact (eq_refl (term612 A u _60240)). Qed.
Lemma lem4863944 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term847 A u f _60240 P _60241) = (term852 A u P f _60240 _60241).
Proof. exact (MK_COMB (@lem4863943 A u _60240) (@lem4863937 A P f _60240 _60241)). Qed.
Lemma lem4863948 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4863949 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term852 A u P f _60240 _60241) = (term854 A P u f _60240 _60241).
Proof. exact (@lem4863948 (@I ((A -> Prop) -> Prop) P _60241) (term565 A u _60240) (term568 A f _60240 _60241)). Qed.
Lemma lem4863965 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term847 A u f _60240 P _60241) = (term854 A P u f _60240 _60241).
Proof. exact (TRANS (@lem4863944 A u P f _60240 _60241) (@lem4863949 A P u f _60240 _60241)). Qed.
Lemma lem4863966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4863967 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term855 A u f _60240 P _60241) = (term856 A P u f _60240 _60241).
Proof. exact (MK_COMB (@lem4863966) (@lem4863965 A P u f _60240 _60241)). Qed.
Lemma lem4863983 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term854 A P u f _60240 _60241) = (term854 A P u f _60240 _60241).
Proof. exact (eq_refl (term854 A P u f _60240 _60241)). Qed.
Lemma lem4863984 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : ((term847 A u f _60240 P _60241) = (term854 A P u f _60240 _60241)) = ((term854 A P u f _60240 _60241) = (term854 A P u f _60240 _60241)).
Proof. exact (MK_COMB (@lem4863967 A P u f _60240 _60241) (@lem4863983 A P u f _60240 _60241)). Qed.
Lemma lem4863986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4863987 (x : Prop) : (x = x) = True.
Proof. exact (@lem4863986 Prop x). Qed.
Lemma lem4863988 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : ((term854 A P u f _60240 _60241) = (term854 A P u f _60240 _60241)) = True.
Proof. exact (@lem4863987 (term854 A P u f _60240 _60241)). Qed.
Lemma lem4863989 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : ((term847 A u f _60240 P _60241) = (term854 A P u f _60240 _60241)) = True.
Proof. exact (TRANS (@lem4863984 A P u f _60240 _60241) (@lem4863988 A P u f _60240 _60241)). Qed.
Lemma lem4863990 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : True = ((term847 A u f _60240 P _60241) = (term854 A P u f _60240 _60241)).
Proof. exact (SYM (@lem4863989 A P u f _60240 _60241)). Qed.
Lemma lem4863991 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term847 A u f _60240 P _60241) = (term854 A P u f _60240 _60241).
Proof. exact (EQ_MP (@lem4863990 A P u f _60240 _60241) (@lem0)). Qed.
Lemma lem4863992 {A : Type'} (_60240 : A -> Prop) (_60241 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term854 A P u f _60240 _60241.
Proof. exact (EQ_MP (@lem4863991 A P u f _60240 _60241) (@lem4863870 A _60240 _60241 P t' f u h1)). Qed.
Lemma lem4863994 (b : Prop) (a : Prop) : (a \/ b) = (term857 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4863995 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (P : type686 A) (_60241 : A -> Prop) : (term854 A P u f _60240 _60241) = (term858 A u f _60240 P _60241).
Proof. exact (@lem4863994 (term859 A u f _60240 _60241) (@I ((A -> Prop) -> Prop) P _60241)). Qed.
Lemma lem4863997 (a : Prop) (b : Prop) : (term860 a b) = (term861 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4863998 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term862 A u f _60240 _60241) = (term863 A u f _60240 _60241).
Proof. exact (@lem4863997 (term565 A u _60240) (term568 A f _60240 _60241)). Qed.
Lemma lem4864000 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4864001 {A : Type'} (u : type686 A) (_60240 : A -> Prop) : (term864 A u _60240) = (@I ((A -> Prop) -> Prop) u _60240).
Proof. exact (@lem4864000 (@I ((A -> Prop) -> Prop) u _60240)). Qed.
Lemma lem4864002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864003 {A : Type'} (u : type686 A) (_60240 : A -> Prop) : (term865 A u _60240) = (term563 A u _60240).
Proof. exact (MK_COMB (@lem4864002) (@lem4864001 A u _60240)). Qed.
Lemma lem4864005 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4864006 {A : Type'} (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term866 A f _60240 _60241) = (term562 A f _60240 _60241).
Proof. exact (@lem4864005 (term562 A f _60240 _60241)). Qed.
Lemma lem4864007 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term863 A u f _60240 _60241) = (term564 A u f _60240 _60241).
Proof. exact (MK_COMB (@lem4864003 A u _60240) (@lem4864006 A f _60240 _60241)). Qed.
Lemma lem4864008 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term862 A u f _60240 _60241) = (term564 A u f _60240 _60241).
Proof. exact (TRANS (@lem4863998 A u f _60240 _60241) (@lem4864007 A u f _60240 _60241)). Qed.
Lemma lem4864009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864010 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (_60241 : A -> Prop) : (term867 A u f _60240 _60241) = (term868 A u f _60240 _60241).
Proof. exact (MK_COMB (@lem4864009) (@lem4864008 A u f _60240 _60241)). Qed.
Lemma lem4864011 {A : Type'} (P : type686 A) (_60241 : A -> Prop) : (@I ((A -> Prop) -> Prop) P _60241) = (@I ((A -> Prop) -> Prop) P _60241).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) P _60241)). Qed.
Lemma lem4864012 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (P : type686 A) (_60241 : A -> Prop) : (term858 A u f _60240 P _60241) = (term869 A u f _60240 P _60241).
Proof. exact (MK_COMB (@lem4864010 A u f _60240 _60241) (@lem4864011 A P _60241)). Qed.
Lemma lem4864013 {A : Type'} (u : type686 A) (f : type639 A) (_60240 : A -> Prop) (P : type686 A) (_60241 : A -> Prop) : (term854 A P u f _60240 _60241) = (term869 A u f _60240 P _60241).
Proof. exact (TRANS (@lem4863995 A u f _60240 P _60241) (@lem4864012 A u f _60240 P _60241)). Qed.
Lemma lem4864015 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term311 A u f s t) : term564 A u f s t.
Proof. exact (conj (@lem4863913 A u f s t h1) (@lem4863920 A u f s t h1)). Qed.
Lemma lem4864017 {A : Type'} (_60240 : A -> Prop) (_60241 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term869 A u f _60240 P _60241.
Proof. exact (EQ_MP (@lem4864013 A u f _60240 P _60241) (@lem4863992 A _60240 _60241 P t' f u h1)). Qed.
Lemma lem4864018 {A : Type'} (_60240 : A -> Prop) (_60241 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term869 A u f _60240 P _60241.
Proof. exact (@lem4864017 A _60240 _60241 P t' f u h1). Qed.
Lemma lem4864019 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term869 A u f s P t.
Proof. exact (@lem4864018 A s t P t' f u h1). Qed.
Lemma lem4864022 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term558 A P t' f u) (h2 : term311 A u f s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (@lem4864019 A s t P t' f u h1 (@lem4864015 A u f s t h2)). Qed.
Lemma lem4864023 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term558 A P t' f u) (h2 : term311 A u f s t) : term848 A P t.
Proof. exact (fun h0 : term565 A P t => @lem4864022 A P t' u f s t h1 h2). Qed.
Lemma lem4864025 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4864026 {A : Type'} (P : type686 A) (t : A -> Prop) : (term848 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4864025 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4864027 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term558 A P t' f u) (h2 : term311 A u f s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4864026 A P t) (@lem4864023 A P t' u f s t h1 h2)). Qed.
Lemma lem4864030 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4864032 {A : Type'} (P : type686 A) (t : A -> Prop) : (term565 A P t) = (term870 A P t).
Proof. exact (@lem4864030 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4864035 {A : Type'} (P : type686 A) (t : A -> Prop) (h1 : term340 A P t) : term870 A P t.
Proof. exact (EQ_MP (@lem4864032 A P t) (@lem4863848 A P t h1)). Qed.
Lemma lem4864038 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term558 A P t' f u) (h3 : term311 A u f s t) : False.
Proof. exact (@lem4864035 A P t h1 (@lem4864027 A P t' u f s t h2 h3)). Qed.
Lemma lem4864039 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term558 A P t' f u) (h3 : term311 A u f s t) : term871.
Proof. exact (fun h0 : ~ False => @lem4864038 A P t' u f s t h1 h2 h3). Qed.
Lemma lem4864041 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4864042 : term871 = False.
Proof. exact (@lem4864041 False). Qed.
Lemma lem4864043 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term558 A P t' f u) (h3 : term311 A u f s t) : False.
Proof. exact (EQ_MP (@lem4864042) (@lem4864039 A P t' u f s t h1 h2 h3)). Qed.
Lemma lem4864044 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : False.
Proof. exact (ex_elim (@lem4863143 A P f u h2) (fun t' : type667 A => fun h0 : term560 A P f u t' => @lem4864043 A P t' u f s t h1 h0 h3)). Qed.
Lemma lem4864045 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : (term340 A P t) = False.
Proof. exact (prop_ext (fun h4 : term340 A P t => @lem4864044 A P u f s t h1 h2 h3) (fun h4 : False => @lem4863159 A P t h1)). Qed.
Lemma lem4864046 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : False.
Proof. exact (EQ_MP (@lem4864045 A P u f s t h1 h2 h3) (@lem4863159 A P t h1)). Qed.
Lemma lem4864047 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : (term311 A u f s t) = False.
Proof. exact (prop_ext (fun h4 : term311 A u f s t => @lem4864046 A P u f s t h1 h2 h3) (fun h4 : False => @lem4863153 A u f s t h3)). Qed.
Lemma lem4864048 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : False.
Proof. exact (EQ_MP (@lem4864047 A P u f s t h1 h2 h3) (@lem4863153 A u f s t h3)). Qed.
Lemma lem4864049 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : (term340 A P t) = False.
Proof. exact (prop_ext (fun h4 : term340 A P t => @lem4864048 A P u f s t h1 h2 h3) (fun h4 : False => @lem4862506 A P t h1)). Qed.
Lemma lem4864050 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term340 A P t) (h2 : term307 A P f u) (h3 : term311 A u f s t) : False.
Proof. exact (EQ_MP (@lem4864049 A P u f s t h1 h2 h3) (@lem4862506 A P t h1)). Qed.
Lemma lem4864051 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A P f u) (h2 : term311 A u f s t) : term339 A P t.
Proof. exact (fun h0 : term340 A P t => @lem4864050 A P u f s t h0 h1 h2). Qed.
Lemma lem4864052 {A : Type'} (P : type686 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A P f u) (h2 : term311 A u f s t) : P t.
Proof. exact (EQ_MP (@lem4862505 A P t) (@lem4864051 A P u f s t h1 h2)). Qed.
Lemma lem4864053 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term313 A u f s P t.
Proof. exact (fun h0 : term311 A u f s t => @lem4864052 A P u f s t h1 h0). Qed.
Lemma lem4864058 {A : Type'} (s : A -> Prop) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term315 A u f s P.
Proof. exact (fun t : A -> Prop => @lem4864053 A s t P f u h1). Qed.
Lemma lem4864063 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term317 A u f P.
Proof. exact (fun s : A -> Prop => @lem4864058 A s P f u h1). Qed.
Lemma lem4864064 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term318 A u f P.
Proof. exact (fun h0 : term307 A P f u => @lem4864063 A P f u h0). Qed.
Lemma lem4864069 {A : Type'} (f : type639 A) (P : type686 A) : term330 A f P.
Proof. exact (fun u : type686 A => @lem4864064 A u f P). Qed.
Lemma lem4864074 {A : Type'} (P : type686 A) : term334 A P.
Proof. exact (fun f : type639 A => @lem4864069 A f P). Qed.
Lemma lem4864079 {A : Type'} : term338 A.
Proof. exact (fun P : type686 A => @lem4864074 A P). Qed.
Lemma lem4864080 {A : Type'} : term337 A.
Proof. exact (EQ_MP (@lem4862499 A) (@lem4864079 A)). Qed.
Lemma lem4864081 {A : Type'} (P : type686 A) : term872 A P.
Proof. exact (@lem4864080 A P). Qed.
Lemma lem4864082 {A : Type'} (P : type686 A) : (term872 A P) = (term333 A P).
Proof. exact (eq_refl (term872 A P)). Qed.
Lemma lem4864083 {A : Type'} (P : type686 A) : term333 A P.
Proof. exact (EQ_MP (@lem4864082 A P) (@lem4864081 A P)). Qed.
Lemma lem4864084 {A : Type'} (P : type686 A) (f : type639 A) : term873 A P f.
Proof. exact (@lem4864083 A P f). Qed.
Lemma lem4864085 {A : Type'} (f : type639 A) (P : type686 A) : (term873 A P f) = (term329 A f P).
Proof. exact (eq_refl (term873 A P f)). Qed.
Lemma lem4864086 {A : Type'} (f : type639 A) (P : type686 A) : term329 A f P.
Proof. exact (EQ_MP (@lem4864085 A f P) (@lem4864084 A P f)). Qed.
Lemma lem4864087 {A : Type'} (f : type639 A) (P : type686 A) (u : type686 A) : term874 A f P u.
Proof. exact (@lem4864086 A f P u). Qed.
Lemma lem4864088 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : (term874 A f P u) = (term320 A u f P).
Proof. exact (eq_refl (term874 A f P u)). Qed.
Lemma lem4864089 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term320 A u f P.
Proof. exact (EQ_MP (@lem4864088 A u f P) (@lem4864087 A f P u)). Qed.
Lemma lem4864091 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term320 A u f P.
Proof. exact (@lem4862225 A u f P (@lem4864089 A u f P)). Qed.
Lemma lem4864092 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term321 A u f P) : False.
Proof. exact (@lem4864091 A u f P (@lem4862209 A u f P h1)). Qed.
Lemma lem4864093 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term321 A u f P) : (term321 A u f P) = False.
Proof. exact (prop_ext (fun h2 : term321 A u f P => @lem4864092 A u f P h1) (fun h2 : False => @lem4862209 A u f P h1)). Qed.
Lemma lem4864094 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) (h1 : term321 A u f P) : False.
Proof. exact (EQ_MP (@lem4864093 A u f P h1) (@lem4862209 A u f P h1)). Qed.
Lemma lem4864095 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term320 A u f P.
Proof. exact (fun h0 : term321 A u f P => @lem4864094 A u f P h0). Qed.
Lemma lem4864096 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term318 A u f P.
Proof. exact (EQ_MP (@lem4862208 A u f P) (@lem4864095 A u f P)). Qed.
Lemma lem4864097 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term273 A u f P.
Proof. exact (EQ_MP (@lem4862204 A u f P) (@lem4864096 A u f P)). Qed.
Lemma lem4864098 {A : Type'} (u : type686 A) (f : type639 A) (P : type686 A) : term272 A u f P.
Proof. exact (EQ_MP (@lem4862032 A u f P) (@lem4864097 A u f P)). Qed.
Lemma lem4864099 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term249 A u f P.
Proof. exact (@lem4864098 A u f P (@lem4861954 A P f u h1 h2)). Qed.
Lemma lem4864103 {_89422 _89438 : Type'} (s : _89438 -> Prop) (f : type1470 _89422 _89438) : (term10 _89422 _89438 f s) = (term11 _89422 _89438 s f).
Proof. exact (EQ_MP (@lem4860997 _89422 _89438 s f) (@lem4860996 _89422 _89438 f s)). Qed.
Lemma lem4864104 {A : Type'} (s : type1171 A) (f : type1170 A) : (term875 A f s) = (term876 A s f).
Proof. exact (@lem4864103 A (type1643 A) s f). Qed.
Lemma lem4864105 {A : Type'} (u : type686 A) (f : type639 A) : (term252 A u f) = (term877 A u f).
Proof. exact (@lem4864104 A (term191 A u f) (@snd (A -> Prop) (A -> Prop))). Qed.
Lemma lem4864126 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4864127 {A : Type'} (u : type686 A) (f : type639 A) : (term878 A u f) = (term879 A u f).
Proof. exact (MK_COMB (@lem4864126 A) (@lem4864105 A u f)). Qed.
Lemma lem4864128 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4864129 {A : Type'} (f : type639 A) (u : type686 A) : ((term252 A u f) = (@UNIONS A u)) = ((term877 A u f) = (@UNIONS A u)).
Proof. exact (MK_COMB (@lem4864127 A u f) (@lem4864128 A u)). Qed.
Lemma lem4864132 {A : Type'} (f : type639 A) (u : type686 A) : ((term877 A u f) = (@UNIONS A u)) = ((term252 A u f) = (@UNIONS A u)).
Proof. exact (SYM (@lem4864129 A f u)). Qed.
Lemma lem4864140 {_89212 _89213 _89357 : Type'} (P : type1470 _89212 _89213) (Q : _89357 -> Prop) (f : type1469 _89212 _89213 _89357) : (term5 _89212 _89213 _89357 P f Q) = (term6 _89212 _89213 _89357 P Q f).
Proof. exact (EQ_MP (@lem4860984 _89212 _89213 _89357 P Q f) (@lem4860983 _89212 _89213 _89357 P Q f)). Qed.
Lemma lem4864141 {A : Type'} (P : type639 A) (Q : type1171 A) (f : type637 A) : (term880 A P f Q) = (term881 A P Q f).
Proof. exact (@lem4864140 (A -> Prop) (A -> Prop) (type1643 A) P Q f). Qed.
Lemma lem4864142 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term882 A u f y) = (term883 A u f y).
Proof. exact (@lem4864141 A (term196 A u f) (term884 A y) (@pair (A -> Prop) (A -> Prop))). Qed.
Lemma lem4864143 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term198 A u f s) = (term199 A u f s).
Proof. exact (eq_refl (term198 A u f s)). Qed.
Lemma lem4864144 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4864145 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term200 A u f s t) = (term201 A u f s t).
Proof. exact (MK_COMB (@lem4864143 A u f s) (@lem4864144 A t)). Qed.
Lemma lem4864146 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term201 A u f s t) = (term202 A u t f s).
Proof. exact (eq_refl (term201 A u f s t)). Qed.
Lemma lem4864147 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term200 A u f s t) = (term202 A u t f s).
Proof. exact (TRANS (@lem4864145 A u f s t) (@lem4864146 A u t f s)). Qed.
Lemma lem4864148 {A : Type'} (GEN_PVAR_212 : type1643 A) : (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212) = (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212).
Proof. exact (eq_refl (@SETSPEC (prod (A -> Prop) (A -> Prop)) GEN_PVAR_212)). Qed.
Lemma lem4864149 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term203 A GEN_PVAR_212 u f s t) = (term204 A GEN_PVAR_212 u t f s).
Proof. exact (MK_COMB (@lem4864148 A GEN_PVAR_212) (@lem4864147 A u t f s)). Qed.
Lemma lem4864150 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@pair (A -> Prop) (A -> Prop) s t) = (@pair (A -> Prop) (A -> Prop) s t).
Proof. exact (eq_refl (@pair (A -> Prop) (A -> Prop) s t)). Qed.
Lemma lem4864151 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term205 A GEN_PVAR_212 u f s t) = (term206 A GEN_PVAR_212 u f s t).
Proof. exact (MK_COMB (@lem4864149 A GEN_PVAR_212 u t f s) (@lem4864150 A s t)). Qed.
Lemma lem4864152 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term207 A GEN_PVAR_212 u f s) = (term208 A GEN_PVAR_212 u f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864151 A GEN_PVAR_212 u f s t)). Qed.
Lemma lem4864153 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864154 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) (s : A -> Prop) : (term209 A GEN_PVAR_212 u f s) = (term210 A GEN_PVAR_212 u f s).
Proof. exact (MK_COMB (@lem4864153 A) (@lem4864152 A GEN_PVAR_212 u f s)). Qed.
Lemma lem4864155 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) : (term211 A GEN_PVAR_212 u f) = (term212 A GEN_PVAR_212 u f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4864154 A GEN_PVAR_212 u f s)). Qed.
Lemma lem4864156 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864157 {A : Type'} (GEN_PVAR_212 : type1643 A) (u : type686 A) (f : type639 A) : (term213 A GEN_PVAR_212 u f) = (term214 A GEN_PVAR_212 u f).
Proof. exact (MK_COMB (@lem4864156 A) (@lem4864155 A GEN_PVAR_212 u f)). Qed.
Lemma lem4864158 {A : Type'} (u : type686 A) (f : type639 A) : (term215 A u f) = (term216 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_212 : type1643 A => @lem4864157 A GEN_PVAR_212 u f)). Qed.
Lemma lem4864159 {A : Type'} : (@GSPEC (prod (A -> Prop) (A -> Prop))) = (@GSPEC (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@GSPEC (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4864160 {A : Type'} (u : type686 A) (f : type639 A) : (term217 A u f) = (term191 A u f).
Proof. exact (MK_COMB (@lem4864159 A) (@lem4864158 A u f)). Qed.
Lemma lem4864161 {A : Type'} (x : type1643 A) : (@IN (prod (A -> Prop) (A -> Prop)) x) = (@IN (prod (A -> Prop) (A -> Prop)) x).
Proof. exact (eq_refl (@IN (prod (A -> Prop) (A -> Prop)) x)). Qed.
Lemma lem4864162 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term218 A x u f) = (term219 A x u f).
Proof. exact (MK_COMB (@lem4864161 A x) (@lem4864160 A u f)). Qed.
Lemma lem4864163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864164 {A : Type'} (x : type1643 A) (u : type686 A) (f : type639 A) : (term885 A x u f) = (term886 A x u f).
Proof. exact (MK_COMB (@lem4864163) (@lem4864162 A x u f)). Qed.
Lemma lem4864165 {A : Type'} (y : A) (x : type1643 A) : (term887 A y x) = (term888 A y x).
Proof. exact (eq_refl (term887 A y x)). Qed.
Lemma lem4864166 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (x : type1643 A) : (term889 A u f y x) = (term890 A u f y x).
Proof. exact (MK_COMB (@lem4864164 A x u f) (@lem4864165 A y x)). Qed.
Lemma lem4864167 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term891 A u f y) = (term892 A u f y).
Proof. exact (fun_ext (fun x : type1643 A => @lem4864166 A u f y x)). Qed.
Lemma lem4864168 {A : Type'} : (@ex (prod (A -> Prop) (A -> Prop))) = (@ex (prod (A -> Prop) (A -> Prop))).
Proof. exact (eq_refl (@ex (prod (A -> Prop) (A -> Prop)))). Qed.
Lemma lem4864169 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term882 A u f y) = (term893 A u f y).
Proof. exact (MK_COMB (@lem4864168 A) (@lem4864167 A u f y)). Qed.
Lemma lem4864170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864171 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term894 A u f y) = (term895 A u f y).
Proof. exact (MK_COMB (@lem4864170) (@lem4864169 A u f y)). Qed.
Lemma lem4864172 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) : (term198 A u f s) = (term199 A u f s).
Proof. exact (eq_refl (term198 A u f s)). Qed.
Lemma lem4864173 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4864174 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term200 A u f s t) = (term201 A u f s t).
Proof. exact (MK_COMB (@lem4864172 A u f s) (@lem4864173 A t)). Qed.
Lemma lem4864175 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term201 A u f s t) = (term202 A u t f s).
Proof. exact (eq_refl (term201 A u f s t)). Qed.
Lemma lem4864176 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term200 A u f s t) = (term202 A u t f s).
Proof. exact (TRANS (@lem4864174 A u f s t) (@lem4864175 A u t f s)). Qed.
Lemma lem4864177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864178 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term896 A u f s t) = (term897 A u t f s).
Proof. exact (MK_COMB (@lem4864177) (@lem4864176 A u t f s)). Qed.
Lemma lem4864179 {A : Type'} (y : A) (s : A -> Prop) (t : A -> Prop) : (term898 A y s t) = (term899 A y s t).
Proof. exact (eq_refl (term898 A y s t)). Qed.
Lemma lem4864180 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) (t : A -> Prop) : (term900 A u f y s t) = (term901 A u f y s t).
Proof. exact (MK_COMB (@lem4864178 A u t f s) (@lem4864179 A y s t)). Qed.
Lemma lem4864181 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) : (term902 A u f y s) = (term903 A u f y s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864180 A u f y s t)). Qed.
Lemma lem4864182 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864183 {A : Type'} (u : type686 A) (f : type639 A) (y : A) (s : A -> Prop) : (term904 A u f y s) = (term905 A u f y s).
Proof. exact (MK_COMB (@lem4864182 A) (@lem4864181 A u f y s)). Qed.
Lemma lem4864184 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term906 A u f y) = (term907 A u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4864183 A u f y s)). Qed.
Lemma lem4864185 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864186 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term883 A u f y) = (term908 A u f y).
Proof. exact (MK_COMB (@lem4864185 A) (@lem4864184 A u f y)). Qed.
Lemma lem4864187 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : ((term882 A u f y) = (term883 A u f y)) = ((term893 A u f y) = (term908 A u f y)).
Proof. exact (MK_COMB (@lem4864171 A u f y) (@lem4864186 A u f y)). Qed.
Lemma lem4864188 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term893 A u f y) = (term908 A u f y).
Proof. exact (EQ_MP (@lem4864187 A u f y) (@lem4864142 A u f y)). Qed.
Lemma lem4864202 {A B : Type'} (x : A) (y : B) : (term243 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem4864203 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term244 A x y) = y.
Proof. exact (@lem4864202 (A -> Prop) (A -> Prop) x y). Qed.
Lemma lem4864204 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term244 A s t) = t.
Proof. exact (@lem4864203 A s t). Qed.
Lemma lem4864205 {A : Type'} (y : A) : (@IN A y) = (@IN A y).
Proof. exact (eq_refl (@IN A y)). Qed.
Lemma lem4864206 {A : Type'} (s : A -> Prop) (y : A) (t : A -> Prop) : (term899 A y s t) = (@IN A y t).
Proof. exact (MK_COMB (@lem4864205 A y) (@lem4864204 A s t)). Qed.
Lemma lem4864207 {A : Type'} (u : type686 A) (t : A -> Prop) (f : type639 A) (s : A -> Prop) : (term897 A u t f s) = (term897 A u t f s).
Proof. exact (eq_refl (term897 A u t f s)). Qed.
Lemma lem4864208 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) (t : A -> Prop) : (term901 A u f y s t) = (term909 A u f s y t).
Proof. exact (MK_COMB (@lem4864207 A u t f s) (@lem4864206 A s y t)). Qed.
Lemma lem4864211 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) : (term903 A u f y s) = (term910 A u f s y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864208 A u f s y t)). Qed.
Lemma lem4864212 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864213 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (y : A) : (term905 A u f y s) = (term911 A u f s y).
Proof. exact (MK_COMB (@lem4864212 A) (@lem4864211 A u f s y)). Qed.
Lemma lem4864218 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term907 A u f y) = (term912 A u f y).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4864213 A u f s y)). Qed.
Lemma lem4864219 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864220 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term908 A u f y) = (term913 A u f y).
Proof. exact (MK_COMB (@lem4864219 A) (@lem4864218 A u f y)). Qed.
Lemma lem4864225 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term893 A u f y) = (term913 A u f y).
Proof. exact (TRANS (@lem4864188 A u f y) (@lem4864220 A u f y)). Qed.
Lemma lem4864226 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4864227 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term914 A GEN_PVAR_47 u f y) = (term915 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4864226 A GEN_PVAR_47) (@lem4864225 A u f y)). Qed.
Lemma lem4864228 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4864229 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term916 A GEN_PVAR_47 u f y) = (term917 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4864227 A GEN_PVAR_47 u f y) (@lem4864228 A y)). Qed.
Lemma lem4864230 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term918 A GEN_PVAR_47 u f) = (term919 A GEN_PVAR_47 u f).
Proof. exact (fun_ext (fun y : A => @lem4864229 A GEN_PVAR_47 u f y)). Qed.
Lemma lem4864231 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4864232 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term920 A GEN_PVAR_47 u f) = (term921 A GEN_PVAR_47 u f).
Proof. exact (MK_COMB (@lem4864231 A) (@lem4864230 A GEN_PVAR_47 u f)). Qed.
Lemma lem4864237 {A : Type'} (u : type686 A) (f : type639 A) : (term922 A u f) = (term923 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4864232 A GEN_PVAR_47 u f)). Qed.
Lemma lem4864238 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4864239 {A : Type'} (u : type686 A) (f : type639 A) : (term877 A u f) = (term924 A u f).
Proof. exact (MK_COMB (@lem4864238 A) (@lem4864237 A u f)). Qed.
Lemma lem4864240 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4864241 {A : Type'} (u : type686 A) (f : type639 A) : (term879 A u f) = (term925 A u f).
Proof. exact (MK_COMB (@lem4864240 A) (@lem4864239 A u f)). Qed.
Lemma lem4864242 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4864243 {A : Type'} (f : type639 A) (u : type686 A) : ((term877 A u f) = (@UNIONS A u)) = ((term924 A u f) = (@UNIONS A u)).
Proof. exact (MK_COMB (@lem4864241 A u f) (@lem4864242 A u)). Qed.
Lemma lem4864246 {A : Type'} (f : type639 A) (u : type686 A) : ((term924 A u f) = (@UNIONS A u)) = ((term877 A u f) = (@UNIONS A u)).
Proof. exact (SYM (@lem4864243 A f u)). Qed.
Lemma lem4864247 (t1 : Prop) : term926 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4864248 (t1 : Prop) : (term926 t1) = (term927 t1).
Proof. exact (eq_refl (term926 t1)). Qed.
Lemma lem4864249 (t1 : Prop) : term927 t1.
Proof. exact (EQ_MP (@lem4864248 t1) (@lem4864247 t1)). Qed.
Lemma lem4864250 (t1 : Prop) (t2 : Prop) : term928 t1 t2.
Proof. exact (@lem4864249 t1 t2). Qed.
Lemma lem4864251 (t1 : Prop) (t2 : Prop) : (term928 t1 t2) = (term929 t1 t2).
Proof. exact (eq_refl (term928 t1 t2)). Qed.
Lemma lem4864252 (t1 : Prop) (t2 : Prop) : term929 t1 t2.
Proof. exact (EQ_MP (@lem4864251 t1 t2) (@lem4864250 t1 t2)). Qed.
Lemma lem4864253 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term930 t1 t2 t3.
Proof. exact (@lem4864252 t1 t2 t3). Qed.
Lemma lem4864254 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term930 t1 t2 t3) = ((term853 t1 t2 t3) = (term931 t1 t2 t3)).
Proof. exact (eq_refl (term930 t1 t2 t3)). Qed.
Lemma lem4864255 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term853 t1 t2 t3) = (term931 t1 t2 t3).
Proof. exact (EQ_MP (@lem4864254 t1 t2 t3) (@lem4864253 t1 t2 t3)). Qed.
Lemma lem4864256 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term931 t1 t2 t3) = (term853 t1 t2 t3).
Proof. exact (SYM (@lem4864255 t1 t2 t3)). Qed.
Lemma lem4864257 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term254 A P f u.
Proof. exact (conj (@lem4861576 A u P f h1) (@lem4861390 A u h2)). Qed.
Lemma lem4864281 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4864282 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (@lem4864281 A s t). Qed.
Lemma lem4864283 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term256 A f c) = c) = (term257 A f c).
Proof. exact (@lem4864282 A (term256 A f c) c). Qed.
Lemma lem4864292 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term258 A f c P) = (term258 A f c P).
Proof. exact (eq_refl (term258 A f c P)). Qed.
Lemma lem4864293 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term259 A P f c) = (term260 A P f c).
Proof. exact (MK_COMB (@lem4864292 A f c P) (@lem4864283 A f c)). Qed.
Lemma lem4864296 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4864297 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term262 A P f c) = (term263 A P f c).
Proof. exact (MK_COMB (@lem4864296 A f c) (@lem4864293 A P f c)). Qed.
Lemma lem4864300 {A : Type'} (c : A -> Prop) (u : type686 A) : (term63 A c u) = (term63 A c u).
Proof. exact (eq_refl (term63 A c u)). Qed.
Lemma lem4864301 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term153 A u P f c) = (term264 A u P f c).
Proof. exact (MK_COMB (@lem4864300 A c u) (@lem4864297 A P f c)). Qed.
Lemma lem4864304 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term155 A u P f) = (term265 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4864301 A u P f c)). Qed.
Lemma lem4864305 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4864306 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term157 A u P f) = (term266 A u P f).
Proof. exact (MK_COMB (@lem4864305 A) (@lem4864304 A u P f)). Qed.
Lemma lem4864311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864312 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term267 A u P f) = (term268 A u P f).
Proof. exact (MK_COMB (@lem4864311) (@lem4864306 A u P f)). Qed.
Lemma lem4864313 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4864314 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term254 A P f u) = (term269 A P f u).
Proof. exact (MK_COMB (@lem4864312 A u P f) (@lem4864313 A u)). Qed.
Lemma lem4864317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864318 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term270 A P f u) = (term271 A P f u).
Proof. exact (MK_COMB (@lem4864317) (@lem4864314 A P f u)). Qed.
Lemma lem4864322 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4864323 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term255 A s t).
Proof. exact (@lem4864322 A s t). Qed.
Lemma lem4864324 {A : Type'} (f : type639 A) (u : type686 A) : ((term924 A u f) = (@UNIONS A u)) = (term932 A f u).
Proof. exact (@lem4864323 A (term924 A u f) (@UNIONS A u)). Qed.
Lemma lem4864349 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term933 A P f u) = (term934 A P f u).
Proof. exact (MK_COMB (@lem4864318 A P f u) (@lem4864324 A f u)). Qed.
Lemma lem4864352 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term934 A P f u) = (term933 A P f u).
Proof. exact (SYM (@lem4864349 A P f u)). Qed.
Lemma lem4864364 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864365 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864364 (A -> Prop) P x). Qed.
Lemma lem4864366 {A : Type'} (u : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c u) = (u c).
Proof. exact (@lem4864365 A u c). Qed.
Lemma lem4864367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864368 {A : Type'} (u : type686 A) (c : A -> Prop) : (term63 A c u) = (term274 A u c).
Proof. exact (MK_COMB (@lem4864367) (@lem4864366 A u c)). Qed.
Lemma lem4864380 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864381 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864380 (A -> Prop) P x). Qed.
Lemma lem4864382 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term275 A c' f c) = (f c c').
Proof. exact (@lem4864381 A (f c) c'). Qed.
Lemma lem4864383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864384 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term276 A c' f c) = (term277 A f c c').
Proof. exact (MK_COMB (@lem4864383) (@lem4864382 A f c c')). Qed.
Lemma lem4864385 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (P c').
Proof. exact (eq_refl (P c')). Qed.
Lemma lem4864386 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term278 A f c P c') = (term279 A f c P c').
Proof. exact (MK_COMB (@lem4864384 A f c c') (@lem4864385 A P c')). Qed.
Lemma lem4864389 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term280 A f c P) = (term281 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4864386 A f c P c')). Qed.
Lemma lem4864390 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4864391 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term282 A f c P) = (term283 A f c P).
Proof. exact (MK_COMB (@lem4864390 A) (@lem4864389 A f c P)). Qed.
Lemma lem4864396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864397 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term258 A f c P) = (term284 A f c P).
Proof. exact (MK_COMB (@lem4864396) (@lem4864391 A f c P)). Qed.
Lemma lem4864405 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4864406 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (@lem4864405 A s x). Qed.
Lemma lem4864407 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term287 A x f c) = (term288 A f c x).
Proof. exact (@lem4864406 A (f c) x). Qed.
Lemma lem4864415 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864416 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864415 (A -> Prop) P x). Qed.
Lemma lem4864417 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term275 A t f c) = (f c t).
Proof. exact (@lem4864416 A (f c) t). Qed.
Lemma lem4864418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864419 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term289 A t f c) = (term290 A f c t).
Proof. exact (MK_COMB (@lem4864418) (@lem4864417 A f c t)). Qed.
Lemma lem4864421 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864422 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4864421 A P x). Qed.
Lemma lem4864423 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4864422 A t x). Qed.
Lemma lem4864424 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term291 A f c x t) = (term292 A f c t x).
Proof. exact (MK_COMB (@lem4864419 A f c t) (@lem4864423 A t x)). Qed.
Lemma lem4864427 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term293 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864424 A f c t x)). Qed.
Lemma lem4864428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864429 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term288 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4864428 A) (@lem4864427 A f c x)). Qed.
Lemma lem4864434 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term287 A x f c) = (term295 A f c x).
Proof. exact (TRANS (@lem4864407 A f c x) (@lem4864429 A f c x)). Qed.
Lemma lem4864435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864436 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term296 A x f c) = (term297 A f c x).
Proof. exact (MK_COMB (@lem4864435) (@lem4864434 A f c x)). Qed.
Lemma lem4864438 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864439 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4864438 A P x). Qed.
Lemma lem4864440 {A : Type'} (c : A -> Prop) (x : A) : (@IN A x c) = (c x).
Proof. exact (@lem4864439 A c x). Qed.
Lemma lem4864441 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term287 A x f c) = (@IN A x c)) = ((term295 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4864436 A f c x) (@lem4864440 A c x)). Qed.
Lemma lem4864444 {A : Type'} (f : type639 A) (c : A -> Prop) : (term298 A f c) = (term299 A f c).
Proof. exact (fun_ext (fun x : A => @lem4864441 A f c x)). Qed.
Lemma lem4864445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4864446 {A : Type'} (f : type639 A) (c : A -> Prop) : (term257 A f c) = (term300 A f c).
Proof. exact (MK_COMB (@lem4864445 A) (@lem4864444 A f c)). Qed.
Lemma lem4864451 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term260 A P f c) = (term301 A P f c).
Proof. exact (MK_COMB (@lem4864397 A f c P) (@lem4864446 A f c)). Qed.
Lemma lem4864454 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4864455 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term263 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4864454 A f c) (@lem4864451 A P f c)). Qed.
Lemma lem4864458 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term264 A u P f c) = (term303 A u P f c).
Proof. exact (MK_COMB (@lem4864368 A u c) (@lem4864455 A P f c)). Qed.
Lemma lem4864461 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term265 A u P f) = (term304 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4864458 A u P f c)). Qed.
Lemma lem4864462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4864463 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term266 A u P f) = (term305 A u P f).
Proof. exact (MK_COMB (@lem4864462 A) (@lem4864461 A u P f)). Qed.
Lemma lem4864468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864469 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term268 A u P f) = (term306 A u P f).
Proof. exact (MK_COMB (@lem4864468) (@lem4864463 A u P f)). Qed.
Lemma lem4864470 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4864471 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term269 A P f u) = (term307 A P f u).
Proof. exact (MK_COMB (@lem4864469 A u P f) (@lem4864470 A u)). Qed.
Lemma lem4864474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864475 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term271 A P f u) = (term308 A P f u).
Proof. exact (MK_COMB (@lem4864474) (@lem4864471 A P f u)). Qed.
Lemma lem4864483 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term935 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4864484 {A : Type'} (p : A -> Prop) (x : A) : (term935 A x p) = (p x).
Proof. exact (@lem4864483 A p x). Qed.
Lemma lem4864485 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term936 A x u f) = (term937 A u f x).
Proof. exact (@lem4864484 A (term938 A u f) x). Qed.
Lemma lem4864486 {A : Type'} (u : type686 A) (f : type639 A) (y : A) : (term937 A u f y) = (term913 A u f y).
Proof. exact (eq_refl (term937 A u f y)). Qed.
Lemma lem4864487 {A : Type'} (GEN_PVAR_47 : A) : (@SETSPEC A GEN_PVAR_47) = (@SETSPEC A GEN_PVAR_47).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_47)). Qed.
Lemma lem4864488 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term939 A GEN_PVAR_47 u f y) = (term915 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4864487 A GEN_PVAR_47) (@lem4864486 A u f y)). Qed.
Lemma lem4864489 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4864490 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) (y : A) : (term940 A GEN_PVAR_47 u f y) = (term917 A GEN_PVAR_47 u f y).
Proof. exact (MK_COMB (@lem4864488 A GEN_PVAR_47 u f y) (@lem4864489 A y)). Qed.
Lemma lem4864491 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term941 A GEN_PVAR_47 u f) = (term919 A GEN_PVAR_47 u f).
Proof. exact (fun_ext (fun y : A => @lem4864490 A GEN_PVAR_47 u f y)). Qed.
Lemma lem4864492 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4864493 {A : Type'} (GEN_PVAR_47 : A) (u : type686 A) (f : type639 A) : (term942 A GEN_PVAR_47 u f) = (term921 A GEN_PVAR_47 u f).
Proof. exact (MK_COMB (@lem4864492 A) (@lem4864491 A GEN_PVAR_47 u f)). Qed.
Lemma lem4864494 {A : Type'} (u : type686 A) (f : type639 A) : (term943 A u f) = (term923 A u f).
Proof. exact (fun_ext (fun GEN_PVAR_47 : A => @lem4864493 A GEN_PVAR_47 u f)). Qed.
Lemma lem4864495 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem4864496 {A : Type'} (u : type686 A) (f : type639 A) : (term944 A u f) = (term924 A u f).
Proof. exact (MK_COMB (@lem4864495 A) (@lem4864494 A u f)). Qed.
Lemma lem4864497 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4864498 {A : Type'} (x : A) (u : type686 A) (f : type639 A) : (term936 A x u f) = (term945 A x u f).
Proof. exact (MK_COMB (@lem4864497 A x) (@lem4864496 A u f)). Qed.
Lemma lem4864499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864500 {A : Type'} (x : A) (u : type686 A) (f : type639 A) : (term946 A x u f) = (term947 A x u f).
Proof. exact (MK_COMB (@lem4864499) (@lem4864498 A x u f)). Qed.
Lemma lem4864501 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term937 A u f x) = (term913 A u f x).
Proof. exact (eq_refl (term937 A u f x)). Qed.
Lemma lem4864502 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : ((term936 A x u f) = (term937 A u f x)) = ((term945 A x u f) = (term913 A u f x)).
Proof. exact (MK_COMB (@lem4864500 A x u f) (@lem4864501 A u f x)). Qed.
Lemma lem4864503 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term945 A x u f) = (term913 A u f x).
Proof. exact (EQ_MP (@lem4864502 A u f x) (@lem4864485 A u f x)). Qed.
Lemma lem4864517 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864518 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864517 (A -> Prop) P x). Qed.
Lemma lem4864519 {A : Type'} (u : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s u) = (u s).
Proof. exact (@lem4864518 A u s). Qed.
Lemma lem4864520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864521 {A : Type'} (u : type686 A) (s : A -> Prop) : (term309 A s u) = (term310 A u s).
Proof. exact (MK_COMB (@lem4864520) (@lem4864519 A u s)). Qed.
Lemma lem4864523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864524 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864523 (A -> Prop) P x). Qed.
Lemma lem4864525 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term275 A t f s) = (f s t).
Proof. exact (@lem4864524 A (f s) t). Qed.
Lemma lem4864526 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term202 A u t f s) = (term311 A u f s t).
Proof. exact (MK_COMB (@lem4864521 A u s) (@lem4864525 A f s t)). Qed.
Lemma lem4864529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864530 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term897 A u t f s) = (term948 A u f s t).
Proof. exact (MK_COMB (@lem4864529) (@lem4864526 A u f s t)). Qed.
Lemma lem4864532 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864533 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4864532 A P x). Qed.
Lemma lem4864534 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4864533 A t x). Qed.
Lemma lem4864535 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term909 A u f s x t) = (term949 A u f s t x).
Proof. exact (MK_COMB (@lem4864530 A u f s t) (@lem4864534 A t x)). Qed.
Lemma lem4864538 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term910 A u f s x) = (term950 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864535 A u f s t x)). Qed.
Lemma lem4864539 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864540 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term911 A u f s x) = (term951 A u f s x).
Proof. exact (MK_COMB (@lem4864539 A) (@lem4864538 A u f s x)). Qed.
Lemma lem4864545 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term912 A u f x) = (term952 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4864540 A u f s x)). Qed.
Lemma lem4864546 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864547 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term913 A u f x) = (term953 A u f x).
Proof. exact (MK_COMB (@lem4864546 A) (@lem4864545 A u f x)). Qed.
Lemma lem4864552 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term945 A x u f) = (term953 A u f x).
Proof. exact (TRANS (@lem4864503 A u f x) (@lem4864547 A u f x)). Qed.
Lemma lem4864553 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864554 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term947 A x u f) = (term954 A u f x).
Proof. exact (MK_COMB (@lem4864553) (@lem4864552 A u f x)). Qed.
Lemma lem4864556 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4864557 {A : Type'} (s : type686 A) (x : A) : (term285 A x s) = (term286 A s x).
Proof. exact (@lem4864556 A s x). Qed.
Lemma lem4864558 {A : Type'} (u : type686 A) (x : A) : (term285 A x u) = (term286 A u x).
Proof. exact (@lem4864557 A u x). Qed.
Lemma lem4864566 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864567 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4864566 (A -> Prop) P x). Qed.
Lemma lem4864568 {A : Type'} (u : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t u) = (u t).
Proof. exact (@lem4864567 A u t). Qed.
Lemma lem4864569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864570 {A : Type'} (u : type686 A) (t : A -> Prop) : (term309 A t u) = (term310 A u t).
Proof. exact (MK_COMB (@lem4864569) (@lem4864568 A u t)). Qed.
Lemma lem4864572 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4864573 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4864572 A P x). Qed.
Lemma lem4864574 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4864573 A t x). Qed.
Lemma lem4864575 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term955 A u x t) = (term956 A u t x).
Proof. exact (MK_COMB (@lem4864570 A u t) (@lem4864574 A t x)). Qed.
Lemma lem4864578 {A : Type'} (u : type686 A) (x : A) : (term957 A u x) = (term958 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864575 A u t x)). Qed.
Lemma lem4864579 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864580 {A : Type'} (u : type686 A) (x : A) : (term286 A u x) = (term959 A u x).
Proof. exact (MK_COMB (@lem4864579 A) (@lem4864578 A u x)). Qed.
Lemma lem4864585 {A : Type'} (u : type686 A) (x : A) : (term285 A x u) = (term959 A u x).
Proof. exact (TRANS (@lem4864558 A u x) (@lem4864580 A u x)). Qed.
Lemma lem4864586 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term945 A x u f) = (term285 A x u)) = ((term953 A u f x) = (term959 A u x)).
Proof. exact (MK_COMB (@lem4864554 A u f x) (@lem4864585 A u x)). Qed.
Lemma lem4864589 {A : Type'} (f : type639 A) (u : type686 A) : (term960 A f u) = (term961 A f u).
Proof. exact (fun_ext (fun x : A => @lem4864586 A f u x)). Qed.
Lemma lem4864590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4864591 {A : Type'} (f : type639 A) (u : type686 A) : (term932 A f u) = (term962 A f u).
Proof. exact (MK_COMB (@lem4864590 A) (@lem4864589 A f u)). Qed.
Lemma lem4864596 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term934 A P f u) = (term963 A P f u).
Proof. exact (MK_COMB (@lem4864475 A P f u) (@lem4864591 A f u)). Qed.
Lemma lem4864599 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term963 A P f u) = (term934 A P f u).
Proof. exact (SYM (@lem4864596 A P f u)). Qed.
Lemma lem4864601 (p : Prop) : p = (term319 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4864602 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term963 A P f u) = (term964 A P f u).
Proof. exact (@lem4864601 (term963 A P f u)). Qed.
Lemma lem4864603 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term964 A P f u) = (term963 A P f u).
Proof. exact (SYM (@lem4864602 A P f u)). Qed.
Lemma lem4864604 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term965 A P f u) : term965 A P f u.
Proof. exact (h1). Qed.
Lemma lem4864607 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term964 A P f u) : term964 A P f u.
Proof. exact (h1). Qed.
Lemma lem4864608 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term966 A P f u.
Proof. exact (fun h0 : term964 A P f u => @lem4864607 A P f u h0). Qed.
Lemma lem4864609 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term966 A P f u) : term966 A P f u.
Proof. exact (h1). Qed.
Lemma lem4864610 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term964 A P f u) : term964 A P f u.
Proof. exact (h1). Qed.
Lemma lem4864611 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term964 A P f u) (h2 : term966 A P f u) : term964 A P f u.
Proof. exact (@lem4864609 A P f u h2 (@lem4864610 A P f u h1)). Qed.
Lemma lem4864612 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term964 A P f u) : term967 A P f u.
Proof. exact (fun h0 : term966 A P f u => @lem4864611 A P f u h1 h0). Qed.
Lemma lem4864613 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term966 A P f u) : term966 A P f u.
Proof. exact (h1). Qed.
Lemma lem4864614 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term964 A P f u) (h2 : term966 A P f u) : term964 A P f u.
Proof. exact (@lem4864612 A P f u h1 (@lem4864613 A P f u h2)). Qed.
Lemma lem4864615 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term966 A P f u) : term966 A P f u.
Proof. exact (fun h0 : term964 A P f u => @lem4864614 A P f u h0 h1). Qed.
Lemma lem4864616 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term968 A P f u.
Proof. exact (fun h0 : term966 A P f u => @lem4864615 A P f u h0). Qed.
Lemma lem4864619 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term966 A P f u.
Proof. exact (@lem4864616 A P f u (@lem4864608 A P f u)). Qed.
Lemma lem4864620 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term966 A P f u.
Proof. exact (@lem4864619 A P f u). Qed.
Lemma lem4864634 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4864635 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term964 A P f u) = (term969 A P f u).
Proof. exact (@lem4864634 (term965 A P f u)). Qed.
Lemma lem4864637 (t : Prop) : (term326 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4864638 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term969 A P f u) = (term963 A P f u).
Proof. exact (@lem4864637 (term963 A P f u)). Qed.
Lemma lem4864641 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term964 A P f u) = (term963 A P f u).
Proof. exact (TRANS (@lem4864635 A P f u) (@lem4864638 A P f u)). Qed.
Lemma lem4864804 {A : Type'} (f : type639 A) (u : type686 A) : (term970 A f u) = (term971 A f u).
Proof. exact (fun_ext (fun P : type686 A => @lem4864641 A P f u)). Qed.
Lemma lem4864805 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4864806 {A : Type'} (f : type639 A) (u : type686 A) : (term972 A f u) = (term973 A f u).
Proof. exact (MK_COMB (@lem4864805 A) (@lem4864804 A f u)). Qed.
Lemma lem4864811 {A : Type'} (u : type686 A) : (term974 A u) = (term975 A u).
Proof. exact (fun_ext (fun f : type639 A => @lem4864806 A f u)). Qed.
Lemma lem4864812 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4864813 {A : Type'} (u : type686 A) : (term976 A u) = (term977 A u).
Proof. exact (MK_COMB (@lem4864812 A) (@lem4864811 A u)). Qed.
Lemma lem4864818 {A : Type'} : (term978 A) = (term979 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4864813 A u)). Qed.
Lemma lem4864819 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4864828 {A : Type'} : (term980 A) = (term981 A).
Proof. exact (MK_COMB (@lem4864819 A) (@lem4864818 A)). Qed.
Lemma lem4864833 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term956 A u t x) = (term956 A u t x).
Proof. exact (eq_refl (term956 A u t x)). Qed.
Lemma lem4864834 {A : Type'} (u : type686 A) (x : A) : (term958 A u x) = (term958 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864833 A u t x)). Qed.
Lemma lem4864835 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864836 {A : Type'} (u : type686 A) (x : A) : (term959 A u x) = (term959 A u x).
Proof. exact (MK_COMB (@lem4864835 A) (@lem4864834 A u x)). Qed.
Lemma lem4864845 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term949 A u f s t x) = (term949 A u f s t x).
Proof. exact (eq_refl (term949 A u f s t x)). Qed.
Lemma lem4864846 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term950 A u f s x) = (term950 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864845 A u f s t x)). Qed.
Lemma lem4864847 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864848 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term951 A u f s x) = (term951 A u f s x).
Proof. exact (MK_COMB (@lem4864847 A) (@lem4864846 A u f s x)). Qed.
Lemma lem4864849 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term952 A u f x) = (term952 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4864848 A u f s x)). Qed.
Lemma lem4864850 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864851 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term953 A u f x) = (term953 A u f x).
Proof. exact (MK_COMB (@lem4864850 A) (@lem4864849 A u f x)). Qed.
Lemma lem4864852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864853 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term954 A u f x) = (term954 A u f x).
Proof. exact (MK_COMB (@lem4864852) (@lem4864851 A u f x)). Qed.
Lemma lem4864854 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term953 A u f x) = (term959 A u x)) = ((term953 A u f x) = (term959 A u x)).
Proof. exact (MK_COMB (@lem4864853 A u f x) (@lem4864836 A u x)). Qed.
Lemma lem4864855 {A : Type'} (f : type639 A) (u : type686 A) : (term961 A f u) = (term961 A f u).
Proof. exact (fun_ext (fun x : A => @lem4864854 A f u x)). Qed.
Lemma lem4864856 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4864857 {A : Type'} (f : type639 A) (u : type686 A) : (term962 A f u) = (term962 A f u).
Proof. exact (MK_COMB (@lem4864856 A) (@lem4864855 A f u)). Qed.
Lemma lem4864858 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4864859 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4864864 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term292 A f c t x) = (term292 A f c t x).
Proof. exact (eq_refl (term292 A f c t x)). Qed.
Lemma lem4864865 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term294 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4864864 A f c t x)). Qed.
Lemma lem4864866 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4864867 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term295 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4864866 A) (@lem4864865 A f c x)). Qed.
Lemma lem4864868 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4864869 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term297 A f c x) = (term297 A f c x).
Proof. exact (MK_COMB (@lem4864868) (@lem4864867 A f c x)). Qed.
Lemma lem4864870 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = ((term295 A f c x) = (c x)).
Proof. exact (MK_COMB (@lem4864869 A f c x) (@lem4864859 A c x)). Qed.
Lemma lem4864871 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term299 A f c).
Proof. exact (fun_ext (fun x : A => @lem4864870 A f c x)). Qed.
Lemma lem4864872 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4864873 {A : Type'} (f : type639 A) (c : A -> Prop) : (term300 A f c) = (term300 A f c).
Proof. exact (MK_COMB (@lem4864872 A) (@lem4864871 A f c)). Qed.
Lemma lem4864878 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term279 A f c P c') = (term279 A f c P c').
Proof. exact (eq_refl (term279 A f c P c')). Qed.
Lemma lem4864879 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term281 A f c P) = (term281 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4864878 A f c P c')). Qed.
Lemma lem4864880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4864881 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term283 A f c P) = (term283 A f c P).
Proof. exact (MK_COMB (@lem4864880 A) (@lem4864879 A f c P)). Qed.
Lemma lem4864882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864883 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term284 A f c P) = (term284 A f c P).
Proof. exact (MK_COMB (@lem4864882) (@lem4864881 A f c P)). Qed.
Lemma lem4864884 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term301 A P f c).
Proof. exact (MK_COMB (@lem4864883 A f c P) (@lem4864873 A f c)). Qed.
Lemma lem4864887 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4864888 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term302 A P f c).
Proof. exact (MK_COMB (@lem4864887 A f c) (@lem4864884 A P f c)). Qed.
Lemma lem4864891 {A : Type'} (u : type686 A) (c : A -> Prop) : (term274 A u c) = (term274 A u c).
Proof. exact (eq_refl (term274 A u c)). Qed.
Lemma lem4864892 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term303 A u P f c).
Proof. exact (MK_COMB (@lem4864891 A u c) (@lem4864888 A P f c)). Qed.
Lemma lem4864893 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term304 A u P f) = (term304 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4864892 A u P f c)). Qed.
Lemma lem4864894 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4864895 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term305 A u P f) = (term305 A u P f).
Proof. exact (MK_COMB (@lem4864894 A) (@lem4864893 A u P f)). Qed.
Lemma lem4864896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4864897 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term306 A u P f).
Proof. exact (MK_COMB (@lem4864896) (@lem4864895 A u P f)). Qed.
Lemma lem4864898 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term307 A P f u).
Proof. exact (MK_COMB (@lem4864897 A u P f) (@lem4864858 A u)). Qed.
Lemma lem4864899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4864900 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term308 A P f u) = (term308 A P f u).
Proof. exact (MK_COMB (@lem4864899) (@lem4864898 A P f u)). Qed.
Lemma lem4864901 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term963 A P f u) = (term963 A P f u).
Proof. exact (MK_COMB (@lem4864900 A P f u) (@lem4864857 A f u)). Qed.
Lemma lem4864902 {A : Type'} (f : type639 A) (u : type686 A) : (term971 A f u) = (term971 A f u).
Proof. exact (fun_ext (fun P : type686 A => @lem4864901 A P f u)). Qed.
Lemma lem4864903 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4864904 {A : Type'} (f : type639 A) (u : type686 A) : (term973 A f u) = (term973 A f u).
Proof. exact (MK_COMB (@lem4864903 A) (@lem4864902 A f u)). Qed.
Lemma lem4864905 {A : Type'} (u : type686 A) : (term975 A u) = (term975 A u).
Proof. exact (fun_ext (fun f : type639 A => @lem4864904 A f u)). Qed.
Lemma lem4864906 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4864907 {A : Type'} (u : type686 A) : (term977 A u) = (term977 A u).
Proof. exact (MK_COMB (@lem4864906 A) (@lem4864905 A u)). Qed.
Lemma lem4864908 {A : Type'} : (term979 A) = (term979 A).
Proof. exact (fun_ext (fun u : type686 A => @lem4864907 A u)). Qed.
Lemma lem4864909 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4864910 {A : Type'} : (term981 A) = (term981 A).
Proof. exact (MK_COMB (@lem4864909 A) (@lem4864908 A)). Qed.
Lemma lem4864999 {A : Type'} : (term980 A) = (term981 A).
Proof. exact (TRANS (@lem4864828 A) (@lem4864910 A)). Qed.
Lemma lem4865000 {A : Type'} : (term981 A) = (term980 A).
Proof. exact (SYM (@lem4864999 A)). Qed.
Lemma lem4865001 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term307 A P f u.
Proof. exact (h1). Qed.
Lemma lem4865003 (p : Prop) : p = (term319 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4865004 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term953 A u f x) = (term959 A u x)) = (term982 A f u x).
Proof. exact (@lem4865003 ((term953 A u f x) = (term959 A u x))). Qed.
Lemma lem4865005 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term982 A f u x) = ((term953 A u f x) = (term959 A u x)).
Proof. exact (SYM (@lem4865004 A f u x)). Qed.
Lemma lem4865006 {A : Type'} (f : type639 A) (u : type686 A) (x : A) (h1 : term983 A f u x) : term983 A f u x.
Proof. exact (h1). Qed.
Lemma lem4865015 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term279 A f c P c') = (term341 A f c P c').
Proof. exact (@lem17265 (f c c') (P c')). Qed.
Lemma lem4865016 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term281 A f c P) = (term342 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4865015 A f c P c')). Qed.
Lemma lem4865017 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865018 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term283 A f c P) = (term343 A f c P).
Proof. exact (MK_COMB (@lem4865017 A) (@lem4865016 A f c P)). Qed.
Lemma lem4865027 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term344 A f c t x) = (term345 A f c t x).
Proof. exact (@lem17045 (f c t) (t x)). Qed.
Lemma lem4865030 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term292 A f c t x) = (term292 A f c t x).
Proof. exact (eq_refl (term292 A f c t x)). Qed.
Lemma lem4865031 {A : Type'} (P : type686 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4865032 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term348 A f c x) = (term349 A f c x).
Proof. exact (@lem4865031 A (term294 A f c x)). Qed.
Lemma lem4865033 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4865034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4865035 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term351 A f c x t) = (term344 A f c t x).
Proof. exact (MK_COMB (@lem4865034) (@lem4865033 A f c t x)). Qed.
Lemma lem4865036 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term351 A f c x t) = (term345 A f c t x).
Proof. exact (TRANS (@lem4865035 A f c t x) (@lem4865027 A f c t x)). Qed.
Lemma lem4865037 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term352 A f c x) = (term353 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865036 A f c t x)). Qed.
Lemma lem4865038 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865039 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term349 A f c x) = (term354 A f c x).
Proof. exact (MK_COMB (@lem4865038 A) (@lem4865037 A f c x)). Qed.
Lemma lem4865040 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term348 A f c x) = (term354 A f c x).
Proof. exact (TRANS (@lem4865032 A f c x) (@lem4865039 A f c x)). Qed.
Lemma lem4865041 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term294 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865030 A f c t x)). Qed.
Lemma lem4865042 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865043 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term295 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4865042 A) (@lem4865041 A f c x)). Qed.
Lemma lem4865044 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4865045 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (c x).
Proof. exact (eq_refl (c x)). Qed.
Lemma lem4865046 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865047 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term356 A f c x) = (term357 A f c x).
Proof. exact (MK_COMB (@lem4865046) (@lem4865040 A f c x)). Qed.
Lemma lem4865048 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term358 A f c x) = (term359 A f c x).
Proof. exact (MK_COMB (@lem4865047 A f c x) (@lem4865045 A c x)). Qed.
Lemma lem4865049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865050 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term360 A f c x) = (term360 A f c x).
Proof. exact (MK_COMB (@lem4865049) (@lem4865043 A f c x)). Qed.
Lemma lem4865051 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term361 A f c x) = (term361 A f c x).
Proof. exact (MK_COMB (@lem4865050 A f c x) (@lem4865044 A c x)). Qed.
Lemma lem4865052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865053 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term362 A f c x) = (term362 A f c x).
Proof. exact (MK_COMB (@lem4865052) (@lem4865051 A f c x)). Qed.
Lemma lem4865054 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term363 A f c x) = (term364 A f c x).
Proof. exact (MK_COMB (@lem4865053 A f c x) (@lem4865048 A f c x)). Qed.
Lemma lem4865055 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = (term363 A f c x).
Proof. exact (@lem17784 (term295 A f c x) (c x)). Qed.
Lemma lem4865056 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term295 A f c x) = (c x)) = (term364 A f c x).
Proof. exact (TRANS (@lem4865055 A f c x) (@lem4865054 A f c x)). Qed.
Lemma lem4865057 {A : Type'} (f : type639 A) (c : A -> Prop) : (term299 A f c) = (term365 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865056 A f c x)). Qed.
Lemma lem4865058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865059 {A : Type'} (f : type639 A) (c : A -> Prop) : (term300 A f c) = (term366 A f c).
Proof. exact (MK_COMB (@lem4865058 A) (@lem4865057 A f c)). Qed.
Lemma lem4865060 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865061 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term284 A f c P) = (term367 A f c P).
Proof. exact (MK_COMB (@lem4865060) (@lem4865018 A f c P)). Qed.
Lemma lem4865062 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term301 A P f c) = (term368 A P f c).
Proof. exact (MK_COMB (@lem4865061 A f c P) (@lem4865059 A f c)). Qed.
Lemma lem4865064 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4865065 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term302 A P f c) = (term369 A P f c).
Proof. exact (MK_COMB (@lem4865064 A f c) (@lem4865062 A P f c)). Qed.
Lemma lem4865067 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4865068 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term371 A u P f c) = (term372 A u P f c).
Proof. exact (MK_COMB (@lem4865067 A u c) (@lem4865065 A P f c)). Qed.
Lemma lem4865069 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term371 A u P f c).
Proof. exact (@lem17265 (u c) (term302 A P f c)). Qed.
Lemma lem4865070 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term303 A u P f c) = (term372 A u P f c).
Proof. exact (TRANS (@lem4865069 A u P f c) (@lem4865068 A u P f c)). Qed.
Lemma lem4865071 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term304 A u P f) = (term373 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4865070 A u P f c)). Qed.
Lemma lem4865072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865073 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term305 A u P f) = (term374 A u P f).
Proof. exact (MK_COMB (@lem4865072 A) (@lem4865071 A u P f)). Qed.
Lemma lem4865074 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4865075 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865076 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term306 A u P f) = (term375 A u P f).
Proof. exact (MK_COMB (@lem4865075) (@lem4865073 A u P f)). Qed.
Lemma lem4865077 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term376 A P f u).
Proof. exact (MK_COMB (@lem4865076 A u P f) (@lem4865074 A u)). Qed.
Lemma lem4865159 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4865160 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term377 A P Q) = (term378 A P Q).
Proof. exact (@lem4865159 A P Q). Qed.
Lemma lem4865161 {A : Type'} (f : type639 A) (c : A -> Prop) : (term379 A f c) = (term380 A f c).
Proof. exact (@lem4865160 A (term381 A f c) (term382 A f c)). Qed.
Lemma lem4865162 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term383 A f c x) = (term361 A f c x).
Proof. exact (eq_refl (term383 A f c x)). Qed.
Lemma lem4865163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865164 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term384 A f c x) = (term362 A f c x).
Proof. exact (MK_COMB (@lem4865163) (@lem4865162 A f c x)). Qed.
Lemma lem4865165 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term385 A f c x) = (term359 A f c x).
Proof. exact (eq_refl (term385 A f c x)). Qed.
Lemma lem4865166 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term386 A f c x) = (term364 A f c x).
Proof. exact (MK_COMB (@lem4865164 A f c x) (@lem4865165 A f c x)). Qed.
Lemma lem4865167 {A : Type'} (f : type639 A) (c : A -> Prop) : (term387 A f c) = (term365 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865166 A f c x)). Qed.
Lemma lem4865168 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865169 {A : Type'} (f : type639 A) (c : A -> Prop) : (term379 A f c) = (term366 A f c).
Proof. exact (MK_COMB (@lem4865168 A) (@lem4865167 A f c)). Qed.
Lemma lem4865170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865171 {A : Type'} (f : type639 A) (c : A -> Prop) : (term388 A f c) = (term389 A f c).
Proof. exact (MK_COMB (@lem4865170) (@lem4865169 A f c)). Qed.
Lemma lem4865172 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term383 A f c x) = (term361 A f c x).
Proof. exact (eq_refl (term383 A f c x)). Qed.
Lemma lem4865173 {A : Type'} (f : type639 A) (c : A -> Prop) : (term390 A f c) = (term381 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865172 A f c x)). Qed.
Lemma lem4865174 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865175 {A : Type'} (f : type639 A) (c : A -> Prop) : (term391 A f c) = (term392 A f c).
Proof. exact (MK_COMB (@lem4865174 A) (@lem4865173 A f c)). Qed.
Lemma lem4865176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865177 {A : Type'} (f : type639 A) (c : A -> Prop) : (term393 A f c) = (term394 A f c).
Proof. exact (MK_COMB (@lem4865176) (@lem4865175 A f c)). Qed.
Lemma lem4865178 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term385 A f c x) = (term359 A f c x).
Proof. exact (eq_refl (term385 A f c x)). Qed.
Lemma lem4865179 {A : Type'} (f : type639 A) (c : A -> Prop) : (term395 A f c) = (term382 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865178 A f c x)). Qed.
Lemma lem4865180 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865181 {A : Type'} (f : type639 A) (c : A -> Prop) : (term396 A f c) = (term397 A f c).
Proof. exact (MK_COMB (@lem4865180 A) (@lem4865179 A f c)). Qed.
Lemma lem4865182 {A : Type'} (f : type639 A) (c : A -> Prop) : (term380 A f c) = (term398 A f c).
Proof. exact (MK_COMB (@lem4865177 A f c) (@lem4865181 A f c)). Qed.
Lemma lem4865183 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term379 A f c) = (term380 A f c)) = ((term366 A f c) = (term398 A f c)).
Proof. exact (MK_COMB (@lem4865171 A f c) (@lem4865182 A f c)). Qed.
Lemma lem4865184 {A : Type'} (f : type639 A) (c : A -> Prop) : (term366 A f c) = (term398 A f c).
Proof. exact (EQ_MP (@lem4865183 A f c) (@lem4865161 A f c)). Qed.
Lemma lem4865361 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4865362 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term368 A P f c) = (term399 A P f c).
Proof. exact (MK_COMB (@lem4865361 A f c P) (@lem4865184 A f c)). Qed.
Lemma lem4865363 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4865364 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term369 A P f c) = (term400 A P f c).
Proof. exact (MK_COMB (@lem4865363 A f c) (@lem4865362 A P f c)). Qed.
Lemma lem4865365 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4865366 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term372 A u P f c) = (term401 A u P f c).
Proof. exact (MK_COMB (@lem4865365 A u c) (@lem4865364 A P f c)). Qed.
Lemma lem4865367 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term373 A u P f) = (term402 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4865366 A u P f c)). Qed.
Lemma lem4865368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865369 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term374 A u P f) = (term403 A u P f).
Proof. exact (MK_COMB (@lem4865368 A) (@lem4865367 A u P f)). Qed.
Lemma lem4865418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865419 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term375 A u P f) = (term404 A u P f).
Proof. exact (MK_COMB (@lem4865418) (@lem4865369 A u P f)). Qed.
Lemma lem4865420 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4865421 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term376 A P f u) = (term405 A P f u).
Proof. exact (MK_COMB (@lem4865419 A u P f) (@lem4865420 A u)). Qed.
Lemma lem4865423 {A : Type'} (P : A -> Prop) (Q : Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4865424 {A : Type'} (P : type686 A) (Q : Prop) : (term408 A P Q) = (term409 A P Q).
Proof. exact (@lem4865423 (A -> Prop) P Q). Qed.
Lemma lem4865425 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term410 A f c x) = (term411 A f c x).
Proof. exact (@lem4865424 A (term294 A f c x) (term355 A c x)). Qed.
Lemma lem4865426 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4865427 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term412 A f c x) = (term294 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865426 A f c t x)). Qed.
Lemma lem4865428 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865429 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term413 A f c x) = (term295 A f c x).
Proof. exact (MK_COMB (@lem4865428 A) (@lem4865427 A f c x)). Qed.
Lemma lem4865430 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865431 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term414 A f c x) = (term360 A f c x).
Proof. exact (MK_COMB (@lem4865430) (@lem4865429 A f c x)). Qed.
Lemma lem4865432 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4865433 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term410 A f c x) = (term361 A f c x).
Proof. exact (MK_COMB (@lem4865431 A f c x) (@lem4865432 A c x)). Qed.
Lemma lem4865434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865435 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term415 A f c x) = (term416 A f c x).
Proof. exact (MK_COMB (@lem4865434) (@lem4865433 A f c x)). Qed.
Lemma lem4865436 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term350 A f c x t) = (term292 A f c t x).
Proof. exact (eq_refl (term350 A f c x t)). Qed.
Lemma lem4865437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865438 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term417 A f c x t) = (term418 A f c t x).
Proof. exact (MK_COMB (@lem4865437) (@lem4865436 A f c t x)). Qed.
Lemma lem4865439 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term355 A c x).
Proof. exact (eq_refl (term355 A c x)). Qed.
Lemma lem4865440 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term419 A f t c x) = (term420 A f t c x).
Proof. exact (MK_COMB (@lem4865438 A f c t x) (@lem4865439 A c x)). Qed.
Lemma lem4865441 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term421 A f c x) = (term422 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865440 A f t c x)). Qed.
Lemma lem4865442 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865443 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term411 A f c x) = (term423 A f c x).
Proof. exact (MK_COMB (@lem4865442 A) (@lem4865441 A f c x)). Qed.
Lemma lem4865444 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term410 A f c x) = (term411 A f c x)) = ((term361 A f c x) = (term423 A f c x)).
Proof. exact (MK_COMB (@lem4865435 A f c x) (@lem4865443 A f c x)). Qed.
Lemma lem4865445 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term361 A f c x) = (term423 A f c x).
Proof. exact (EQ_MP (@lem4865444 A f c x) (@lem4865425 A f c x)). Qed.
Lemma lem4865446 {A : Type'} (f : type639 A) (c : A -> Prop) : (term381 A f c) = (term424 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865445 A f c x)). Qed.
Lemma lem4865447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865448 {A : Type'} (f : type639 A) (c : A -> Prop) : (term392 A f c) = (term425 A f c).
Proof. exact (MK_COMB (@lem4865447 A) (@lem4865446 A f c)). Qed.
Lemma lem4865450 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4865451 {A : Type'} (P : type1364 A) : (term426 A P) = (term427 A P).
Proof. exact (@lem4865450 A (A -> Prop) P). Qed.
Lemma lem4865452 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term429 A f c).
Proof. exact (@lem4865451 A (term430 A f c)). Qed.
Lemma lem4865453 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term431 A f c x) = (term422 A f c x).
Proof. exact (eq_refl (term431 A f c x)). Qed.
Lemma lem4865454 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4865455 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) (t : A -> Prop) : (term432 A f c x t) = (term433 A f c x t).
Proof. exact (MK_COMB (@lem4865453 A f c x) (@lem4865454 A t)). Qed.
Lemma lem4865456 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term433 A f c x t) = (term420 A f t c x).
Proof. exact (eq_refl (term433 A f c x t)). Qed.
Lemma lem4865457 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term432 A f c x t) = (term420 A f t c x).
Proof. exact (TRANS (@lem4865455 A f c x t) (@lem4865456 A f t c x)). Qed.
Lemma lem4865458 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term434 A f c x) = (term422 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865457 A f t c x)). Qed.
Lemma lem4865459 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865460 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term435 A f c x) = (term423 A f c x).
Proof. exact (MK_COMB (@lem4865459 A) (@lem4865458 A f c x)). Qed.
Lemma lem4865461 {A : Type'} (f : type639 A) (c : A -> Prop) : (term436 A f c) = (term424 A f c).
Proof. exact (fun_ext (fun x : A => @lem4865460 A f c x)). Qed.
Lemma lem4865462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865463 {A : Type'} (f : type639 A) (c : A -> Prop) : (term428 A f c) = (term425 A f c).
Proof. exact (MK_COMB (@lem4865462 A) (@lem4865461 A f c)). Qed.
Lemma lem4865464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865465 {A : Type'} (f : type639 A) (c : A -> Prop) : (term437 A f c) = (term438 A f c).
Proof. exact (MK_COMB (@lem4865464) (@lem4865463 A f c)). Qed.
Lemma lem4865466 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term431 A f c x) = (term422 A f c x).
Proof. exact (eq_refl (term431 A f c x)). Qed.
Lemma lem4865467 {A : Type'} (t : type1402 A) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4865468 {A : Type'} (f : type639 A) (c : A -> Prop) (t : type1402 A) (x : A) : (term439 A f c t x) = (term440 A f c t x).
Proof. exact (MK_COMB (@lem4865466 A f c x) (@lem4865467 A t x)). Qed.
Lemma lem4865469 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term440 A f c t x) = (term441 A f t c x).
Proof. exact (eq_refl (term440 A f c t x)). Qed.
Lemma lem4865470 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) (x : A) : (term439 A f c t x) = (term441 A f t c x).
Proof. exact (TRANS (@lem4865468 A f c t x) (@lem4865469 A f t c x)). Qed.
Lemma lem4865471 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term442 A f c t) = (term443 A f t c).
Proof. exact (fun_ext (fun x : A => @lem4865470 A f t c x)). Qed.
Lemma lem4865472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4865473 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term444 A f c t) = (term445 A f t c).
Proof. exact (MK_COMB (@lem4865472 A) (@lem4865471 A f t c)). Qed.
Lemma lem4865474 {A : Type'} (f : type639 A) (c : A -> Prop) : (term446 A f c) = (term447 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865473 A f t c)). Qed.
Lemma lem4865475 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865476 {A : Type'} (f : type639 A) (c : A -> Prop) : (term429 A f c) = (term448 A f c).
Proof. exact (MK_COMB (@lem4865475 A) (@lem4865474 A f c)). Qed.
Lemma lem4865477 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term428 A f c) = (term429 A f c)) = ((term425 A f c) = (term448 A f c)).
Proof. exact (MK_COMB (@lem4865465 A f c) (@lem4865476 A f c)). Qed.
Lemma lem4865478 {A : Type'} (f : type639 A) (c : A -> Prop) : (term425 A f c) = (term448 A f c).
Proof. exact (EQ_MP (@lem4865477 A f c) (@lem4865452 A f c)). Qed.
Lemma lem4865479 {A : Type'} (f : type639 A) (c : A -> Prop) : (term392 A f c) = (term448 A f c).
Proof. exact (TRANS (@lem4865448 A f c) (@lem4865478 A f c)). Qed.
Lemma lem4865480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865481 {A : Type'} (f : type639 A) (c : A -> Prop) : (term394 A f c) = (term449 A f c).
Proof. exact (MK_COMB (@lem4865480) (@lem4865479 A f c)). Qed.
Lemma lem4865482 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4865483 {A : Type'} (f : type639 A) (c : A -> Prop) : (term398 A f c) = (term450 A f c).
Proof. exact (MK_COMB (@lem4865481 A f c) (@lem4865482 A f c)). Qed.
Lemma lem4865485 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4865486 {A : Type'} (P : type421 A) (Q : Prop) : (term453 A P Q) = (term454 A P Q).
Proof. exact (@lem4865485 (type1402 A) P Q). Qed.
Lemma lem4865487 {A : Type'} (f : type639 A) (c : A -> Prop) : (term455 A f c) = (term456 A f c).
Proof. exact (@lem4865486 A (term447 A f c) (term397 A f c)). Qed.
Lemma lem4865488 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term457 A f c t) = (term445 A f t c).
Proof. exact (eq_refl (term457 A f c t)). Qed.
Lemma lem4865489 {A : Type'} (f : type639 A) (c : A -> Prop) : (term458 A f c) = (term447 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865488 A f t c)). Qed.
Lemma lem4865490 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865491 {A : Type'} (f : type639 A) (c : A -> Prop) : (term459 A f c) = (term448 A f c).
Proof. exact (MK_COMB (@lem4865490 A) (@lem4865489 A f c)). Qed.
Lemma lem4865492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865493 {A : Type'} (f : type639 A) (c : A -> Prop) : (term460 A f c) = (term449 A f c).
Proof. exact (MK_COMB (@lem4865492) (@lem4865491 A f c)). Qed.
Lemma lem4865494 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4865495 {A : Type'} (f : type639 A) (c : A -> Prop) : (term455 A f c) = (term450 A f c).
Proof. exact (MK_COMB (@lem4865493 A f c) (@lem4865494 A f c)). Qed.
Lemma lem4865496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865497 {A : Type'} (f : type639 A) (c : A -> Prop) : (term461 A f c) = (term462 A f c).
Proof. exact (MK_COMB (@lem4865496) (@lem4865495 A f c)). Qed.
Lemma lem4865498 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term457 A f c t) = (term445 A f t c).
Proof. exact (eq_refl (term457 A f c t)). Qed.
Lemma lem4865499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865500 {A : Type'} (f : type639 A) (t : type1402 A) (c : A -> Prop) : (term463 A f c t) = (term464 A f t c).
Proof. exact (MK_COMB (@lem4865499) (@lem4865498 A f t c)). Qed.
Lemma lem4865501 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term397 A f c).
Proof. exact (eq_refl (term397 A f c)). Qed.
Lemma lem4865502 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term465 A t f c) = (term466 A t f c).
Proof. exact (MK_COMB (@lem4865500 A f t c) (@lem4865501 A f c)). Qed.
Lemma lem4865503 {A : Type'} (f : type639 A) (c : A -> Prop) : (term467 A f c) = (term468 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865502 A t f c)). Qed.
Lemma lem4865504 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865505 {A : Type'} (f : type639 A) (c : A -> Prop) : (term456 A f c) = (term469 A f c).
Proof. exact (MK_COMB (@lem4865504 A) (@lem4865503 A f c)). Qed.
Lemma lem4865506 {A : Type'} (f : type639 A) (c : A -> Prop) : ((term455 A f c) = (term456 A f c)) = ((term450 A f c) = (term469 A f c)).
Proof. exact (MK_COMB (@lem4865497 A f c) (@lem4865505 A f c)). Qed.
Lemma lem4865507 {A : Type'} (f : type639 A) (c : A -> Prop) : (term450 A f c) = (term469 A f c).
Proof. exact (EQ_MP (@lem4865506 A f c) (@lem4865487 A f c)). Qed.
Lemma lem4865508 {A : Type'} (f : type639 A) (c : A -> Prop) : (term398 A f c) = (term469 A f c).
Proof. exact (TRANS (@lem4865483 A f c) (@lem4865507 A f c)). Qed.
Lemma lem4865509 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4865510 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term399 A P f c) = (term470 A P f c).
Proof. exact (MK_COMB (@lem4865509 A f c P) (@lem4865508 A f c)). Qed.
Lemma lem4865512 {A : Type'} (P : Prop) (Q : A -> Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4865513 {A : Type'} (P : Prop) (Q : type421 A) : (term473 A P Q) = (term474 A P Q).
Proof. exact (@lem4865512 (type1402 A) P Q). Qed.
Lemma lem4865514 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term475 A P f c) = (term476 A P f c).
Proof. exact (@lem4865513 A (term343 A f c P) (term468 A f c)). Qed.
Lemma lem4865515 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term477 A f c t) = (term466 A t f c).
Proof. exact (eq_refl (term477 A f c t)). Qed.
Lemma lem4865516 {A : Type'} (f : type639 A) (c : A -> Prop) : (term478 A f c) = (term468 A f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865515 A t f c)). Qed.
Lemma lem4865517 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865518 {A : Type'} (f : type639 A) (c : A -> Prop) : (term479 A f c) = (term469 A f c).
Proof. exact (MK_COMB (@lem4865517 A) (@lem4865516 A f c)). Qed.
Lemma lem4865519 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4865520 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term475 A P f c) = (term470 A P f c).
Proof. exact (MK_COMB (@lem4865519 A f c P) (@lem4865518 A f c)). Qed.
Lemma lem4865521 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865522 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term480 A P f c) = (term481 A P f c).
Proof. exact (MK_COMB (@lem4865521) (@lem4865520 A P f c)). Qed.
Lemma lem4865523 {A : Type'} (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term477 A f c t) = (term466 A t f c).
Proof. exact (eq_refl (term477 A f c t)). Qed.
Lemma lem4865524 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term367 A f c P).
Proof. exact (eq_refl (term367 A f c P)). Qed.
Lemma lem4865525 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term482 A P f c t) = (term483 A P t f c).
Proof. exact (MK_COMB (@lem4865524 A f c P) (@lem4865523 A t f c)). Qed.
Lemma lem4865526 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term484 A P f c) = (term485 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865525 A P t f c)). Qed.
Lemma lem4865527 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865528 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term476 A P f c) = (term486 A P f c).
Proof. exact (MK_COMB (@lem4865527 A) (@lem4865526 A P f c)). Qed.
Lemma lem4865529 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term475 A P f c) = (term476 A P f c)) = ((term470 A P f c) = (term486 A P f c)).
Proof. exact (MK_COMB (@lem4865522 A P f c) (@lem4865528 A P f c)). Qed.
Lemma lem4865530 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term470 A P f c) = (term486 A P f c).
Proof. exact (EQ_MP (@lem4865529 A P f c) (@lem4865514 A P f c)). Qed.
Lemma lem4865531 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term399 A P f c) = (term486 A P f c).
Proof. exact (TRANS (@lem4865510 A P f c) (@lem4865530 A P f c)). Qed.
Lemma lem4865532 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4865533 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term400 A P f c) = (term487 A P f c).
Proof. exact (MK_COMB (@lem4865532 A f c) (@lem4865531 A P f c)). Qed.
Lemma lem4865535 {A : Type'} (P : Prop) (Q : A -> Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4865536 {A : Type'} (P : Prop) (Q : type421 A) : (term473 A P Q) = (term474 A P Q).
Proof. exact (@lem4865535 (type1402 A) P Q). Qed.
Lemma lem4865537 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term488 A P f c) = (term489 A P f c).
Proof. exact (@lem4865536 A (term490 A f c) (term485 A P f c)). Qed.
Lemma lem4865538 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term491 A P f c t) = (term483 A P t f c).
Proof. exact (eq_refl (term491 A P f c t)). Qed.
Lemma lem4865539 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term492 A P f c) = (term485 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865538 A P t f c)). Qed.
Lemma lem4865540 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865541 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term493 A P f c) = (term486 A P f c).
Proof. exact (MK_COMB (@lem4865540 A) (@lem4865539 A P f c)). Qed.
Lemma lem4865542 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4865543 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term488 A P f c) = (term487 A P f c).
Proof. exact (MK_COMB (@lem4865542 A f c) (@lem4865541 A P f c)). Qed.
Lemma lem4865544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865545 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term494 A P f c) = (term495 A P f c).
Proof. exact (MK_COMB (@lem4865544) (@lem4865543 A P f c)). Qed.
Lemma lem4865546 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term491 A P f c t) = (term483 A P t f c).
Proof. exact (eq_refl (term491 A P f c t)). Qed.
Lemma lem4865547 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term261 A f c).
Proof. exact (eq_refl (term261 A f c)). Qed.
Lemma lem4865548 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term496 A P f c t) = (term497 A P t f c).
Proof. exact (MK_COMB (@lem4865547 A f c) (@lem4865546 A P t f c)). Qed.
Lemma lem4865549 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term498 A P f c) = (term499 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865548 A P t f c)). Qed.
Lemma lem4865550 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865551 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term489 A P f c) = (term500 A P f c).
Proof. exact (MK_COMB (@lem4865550 A) (@lem4865549 A P f c)). Qed.
Lemma lem4865552 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term488 A P f c) = (term489 A P f c)) = ((term487 A P f c) = (term500 A P f c)).
Proof. exact (MK_COMB (@lem4865545 A P f c) (@lem4865551 A P f c)). Qed.
Lemma lem4865553 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term487 A P f c) = (term500 A P f c).
Proof. exact (EQ_MP (@lem4865552 A P f c) (@lem4865537 A P f c)). Qed.
Lemma lem4865554 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term400 A P f c) = (term500 A P f c).
Proof. exact (TRANS (@lem4865533 A P f c) (@lem4865553 A P f c)). Qed.
Lemma lem4865555 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4865556 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term401 A u P f c) = (term501 A u P f c).
Proof. exact (MK_COMB (@lem4865555 A u c) (@lem4865554 A P f c)). Qed.
Lemma lem4865558 {A : Type'} (P : Prop) (Q : A -> Prop) : (term502 A P Q) = (term503 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4865559 {A : Type'} (P : Prop) (Q : type421 A) : (term504 A P Q) = (term505 A P Q).
Proof. exact (@lem4865558 (type1402 A) P Q). Qed.
Lemma lem4865560 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term506 A u P f c) = (term507 A u P f c).
Proof. exact (@lem4865559 A (term340 A u c) (term499 A P f c)). Qed.
Lemma lem4865561 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term508 A P f c t) = (term497 A P t f c).
Proof. exact (eq_refl (term508 A P f c t)). Qed.
Lemma lem4865562 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term509 A P f c) = (term499 A P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865561 A P t f c)). Qed.
Lemma lem4865563 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865564 {A : Type'} (P : type686 A) (f : type639 A) (c : A -> Prop) : (term510 A P f c) = (term500 A P f c).
Proof. exact (MK_COMB (@lem4865563 A) (@lem4865562 A P f c)). Qed.
Lemma lem4865565 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4865566 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term506 A u P f c) = (term501 A u P f c).
Proof. exact (MK_COMB (@lem4865565 A u c) (@lem4865564 A P f c)). Qed.
Lemma lem4865567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865568 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term511 A u P f c) = (term512 A u P f c).
Proof. exact (MK_COMB (@lem4865567) (@lem4865566 A u P f c)). Qed.
Lemma lem4865569 {A : Type'} (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term508 A P f c t) = (term497 A P t f c).
Proof. exact (eq_refl (term508 A P f c t)). Qed.
Lemma lem4865570 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term370 A u c).
Proof. exact (eq_refl (term370 A u c)). Qed.
Lemma lem4865571 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term513 A u P f c t) = (term514 A u P t f c).
Proof. exact (MK_COMB (@lem4865570 A u c) (@lem4865569 A P t f c)). Qed.
Lemma lem4865572 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term515 A u P f c) = (term516 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865571 A u P t f c)). Qed.
Lemma lem4865573 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865574 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term507 A u P f c) = (term517 A u P f c).
Proof. exact (MK_COMB (@lem4865573 A) (@lem4865572 A u P f c)). Qed.
Lemma lem4865575 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : ((term506 A u P f c) = (term507 A u P f c)) = ((term501 A u P f c) = (term517 A u P f c)).
Proof. exact (MK_COMB (@lem4865568 A u P f c) (@lem4865574 A u P f c)). Qed.
Lemma lem4865576 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term501 A u P f c) = (term517 A u P f c).
Proof. exact (EQ_MP (@lem4865575 A u P f c) (@lem4865560 A u P f c)). Qed.
Lemma lem4865577 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term401 A u P f c) = (term517 A u P f c).
Proof. exact (TRANS (@lem4865556 A u P f c) (@lem4865576 A u P f c)). Qed.
Lemma lem4865578 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term402 A u P f) = (term518 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4865577 A u P f c)). Qed.
Lemma lem4865579 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865580 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term403 A u P f) = (term519 A u P f).
Proof. exact (MK_COMB (@lem4865579 A) (@lem4865578 A u P f)). Qed.
Lemma lem4865582 {A B : Type'} (P : type1413 A B) : (term30 A B P) = (term31 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4865583 {A : Type'} (P : type611 A) : (term520 A P) = (term521 A P).
Proof. exact (@lem4865582 (A -> Prop) (type1402 A) P). Qed.
Lemma lem4865584 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term522 A u P f) = (term523 A u P f).
Proof. exact (@lem4865583 A (term524 A u P f)). Qed.
Lemma lem4865585 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A u P f c) = (term516 A u P f c).
Proof. exact (eq_refl (term525 A u P f c)). Qed.
Lemma lem4865586 {A : Type'} (t : type1402 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4865587 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) (t : type1402 A) : (term526 A u P f c t) = (term527 A u P f c t).
Proof. exact (MK_COMB (@lem4865585 A u P f c) (@lem4865586 A t)). Qed.
Lemma lem4865588 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term527 A u P f c t) = (term514 A u P t f c).
Proof. exact (eq_refl (term527 A u P f c t)). Qed.
Lemma lem4865589 {A : Type'} (u : type686 A) (P : type686 A) (t : type1402 A) (f : type639 A) (c : A -> Prop) : (term526 A u P f c t) = (term514 A u P t f c).
Proof. exact (TRANS (@lem4865587 A u P f c t) (@lem4865588 A u P t f c)). Qed.
Lemma lem4865590 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term528 A u P f c) = (term516 A u P f c).
Proof. exact (fun_ext (fun t : type1402 A => @lem4865589 A u P t f c)). Qed.
Lemma lem4865591 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4865592 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term529 A u P f c) = (term517 A u P f c).
Proof. exact (MK_COMB (@lem4865591 A) (@lem4865590 A u P f c)). Qed.
Lemma lem4865593 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term530 A u P f) = (term518 A u P f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4865592 A u P f c)). Qed.
Lemma lem4865594 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865595 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term522 A u P f) = (term519 A u P f).
Proof. exact (MK_COMB (@lem4865594 A) (@lem4865593 A u P f)). Qed.
Lemma lem4865596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865597 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term531 A u P f) = (term532 A u P f).
Proof. exact (MK_COMB (@lem4865596) (@lem4865595 A u P f)). Qed.
Lemma lem4865598 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (c : A -> Prop) : (term525 A u P f c) = (term516 A u P f c).
Proof. exact (eq_refl (term525 A u P f c)). Qed.
Lemma lem4865599 {A : Type'} (t : type667 A) (c : A -> Prop) : (t c) = (t c).
Proof. exact (eq_refl (t c)). Qed.
Lemma lem4865600 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) (t : type667 A) (c : A -> Prop) : (term533 A u P f t c) = (term534 A u P f t c).
Proof. exact (MK_COMB (@lem4865598 A u P f c) (@lem4865599 A t c)). Qed.
Lemma lem4865601 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term534 A u P f t c) = (term535 A u P t f c).
Proof. exact (eq_refl (term534 A u P f t c)). Qed.
Lemma lem4865602 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) (c : A -> Prop) : (term533 A u P f t c) = (term535 A u P t f c).
Proof. exact (TRANS (@lem4865600 A u P f t c) (@lem4865601 A u P t f c)). Qed.
Lemma lem4865603 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term536 A u P f t) = (term537 A u P t f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4865602 A u P t f c)). Qed.
Lemma lem4865604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865605 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term538 A u P f t) = (term539 A u P t f).
Proof. exact (MK_COMB (@lem4865604 A) (@lem4865603 A u P t f)). Qed.
Lemma lem4865606 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term540 A u P f) = (term541 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4865605 A u P t f)). Qed.
Lemma lem4865607 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4865608 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term523 A u P f) = (term542 A u P f).
Proof. exact (MK_COMB (@lem4865607 A) (@lem4865606 A u P f)). Qed.
Lemma lem4865609 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : ((term522 A u P f) = (term523 A u P f)) = ((term519 A u P f) = (term542 A u P f)).
Proof. exact (MK_COMB (@lem4865597 A u P f) (@lem4865608 A u P f)). Qed.
Lemma lem4865610 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term519 A u P f) = (term542 A u P f).
Proof. exact (EQ_MP (@lem4865609 A u P f) (@lem4865584 A u P f)). Qed.
Lemma lem4865611 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term403 A u P f) = (term542 A u P f).
Proof. exact (TRANS (@lem4865580 A u P f) (@lem4865610 A u P f)). Qed.
Lemma lem4865612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865613 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term404 A u P f) = (term543 A u P f).
Proof. exact (MK_COMB (@lem4865612) (@lem4865611 A u P f)). Qed.
Lemma lem4865614 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4865615 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term405 A P f u) = (term544 A P f u).
Proof. exact (MK_COMB (@lem4865613 A u P f) (@lem4865614 A u)). Qed.
Lemma lem4865617 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4865618 {A : Type'} (P : type149 A) (Q : Prop) : (term545 A P Q) = (term546 A P Q).
Proof. exact (@lem4865617 (type667 A) P Q). Qed.
Lemma lem4865619 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term547 A P f u) = (term548 A P f u).
Proof. exact (@lem4865618 A (term541 A u P f) (@ARBITRARY A u)). Qed.
Lemma lem4865620 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term549 A u P f t) = (term539 A u P t f).
Proof. exact (eq_refl (term549 A u P f t)). Qed.
Lemma lem4865621 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term550 A u P f) = (term541 A u P f).
Proof. exact (fun_ext (fun t : type667 A => @lem4865620 A u P t f)). Qed.
Lemma lem4865622 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4865623 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term551 A u P f) = (term542 A u P f).
Proof. exact (MK_COMB (@lem4865622 A) (@lem4865621 A u P f)). Qed.
Lemma lem4865624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865625 {A : Type'} (u : type686 A) (P : type686 A) (f : type639 A) : (term552 A u P f) = (term543 A u P f).
Proof. exact (MK_COMB (@lem4865624) (@lem4865623 A u P f)). Qed.
Lemma lem4865626 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4865627 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term547 A P f u) = (term544 A P f u).
Proof. exact (MK_COMB (@lem4865625 A u P f) (@lem4865626 A u)). Qed.
Lemma lem4865628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865629 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term553 A P f u) = (term554 A P f u).
Proof. exact (MK_COMB (@lem4865628) (@lem4865627 A P f u)). Qed.
Lemma lem4865630 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term549 A u P f t) = (term539 A u P t f).
Proof. exact (eq_refl (term549 A u P f t)). Qed.
Lemma lem4865631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865632 {A : Type'} (u : type686 A) (P : type686 A) (t : type667 A) (f : type639 A) : (term555 A u P f t) = (term556 A u P t f).
Proof. exact (MK_COMB (@lem4865631) (@lem4865630 A u P t f)). Qed.
Lemma lem4865633 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@ARBITRARY A u).
Proof. exact (eq_refl (@ARBITRARY A u)). Qed.
Lemma lem4865634 {A : Type'} (P : type686 A) (t : type667 A) (f : type639 A) (u : type686 A) : (term557 A P f t u) = (term558 A P t f u).
Proof. exact (MK_COMB (@lem4865632 A u P t f) (@lem4865633 A u)). Qed.
Lemma lem4865635 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term559 A P f u) = (term560 A P f u).
Proof. exact (fun_ext (fun t : type667 A => @lem4865634 A P t f u)). Qed.
Lemma lem4865636 {A : Type'} : (@ex ((A -> Prop) -> A -> A -> Prop)) = (@ex ((A -> Prop) -> A -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> A -> Prop))). Qed.
Lemma lem4865637 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term548 A P f u) = (term561 A P f u).
Proof. exact (MK_COMB (@lem4865636 A) (@lem4865635 A P f u)). Qed.
Lemma lem4865638 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : ((term547 A P f u) = (term548 A P f u)) = ((term544 A P f u) = (term561 A P f u)).
Proof. exact (MK_COMB (@lem4865629 A P f u) (@lem4865637 A P f u)). Qed.
Lemma lem4865639 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term544 A P f u) = (term561 A P f u).
Proof. exact (EQ_MP (@lem4865638 A P f u) (@lem4865619 A P f u)). Qed.
Lemma lem4865640 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term405 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4865615 A P f u) (@lem4865639 A P f u)). Qed.
Lemma lem4865641 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term376 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4865421 A P f u) (@lem4865640 A P f u)). Qed.
Lemma lem4865642 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term307 A P f u) = (term561 A P f u).
Proof. exact (TRANS (@lem4865077 A P f u) (@lem4865641 A P f u)). Qed.
Lemma lem4865643 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term561 A P f u.
Proof. exact (EQ_MP (@lem4865642 A P f u) (@lem4865001 A P f u h1)). Qed.
Lemma lem4865652 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term984 A u f s t) = (term985 A u f s t).
Proof. exact (@lem17045 (u s) (f s t)). Qed.
Lemma lem4865656 {A : Type'} (t : A -> Prop) (x : A) : (term355 A t x) = (term355 A t x).
Proof. exact (eq_refl (term355 A t x)). Qed.
Lemma lem4865658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865659 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term986 A u f s t) = (term987 A u f s t).
Proof. exact (MK_COMB (@lem4865658) (@lem4865652 A u f s t)). Qed.
Lemma lem4865660 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term988 A u f s t x) = (term989 A u f s t x).
Proof. exact (MK_COMB (@lem4865659 A u f s t) (@lem4865656 A t x)). Qed.
Lemma lem4865661 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term990 A u f s t x) = (term988 A u f s t x).
Proof. exact (@lem17045 (term311 A u f s t) (t x)). Qed.
Lemma lem4865662 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term990 A u f s t x) = (term989 A u f s t x).
Proof. exact (TRANS (@lem4865661 A u f s t x) (@lem4865660 A u f s t x)). Qed.
Lemma lem4865665 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term949 A u f s t x) = (term949 A u f s t x).
Proof. exact (eq_refl (term949 A u f s t x)). Qed.
Lemma lem4865666 {A : Type'} (P : type686 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4865667 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term991 A u f s x) = (term992 A u f s x).
Proof. exact (@lem4865666 A (term950 A u f s x)). Qed.
Lemma lem4865668 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term993 A u f s x t) = (term949 A u f s t x).
Proof. exact (eq_refl (term993 A u f s x t)). Qed.
Lemma lem4865669 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4865670 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term994 A u f s x t) = (term990 A u f s t x).
Proof. exact (MK_COMB (@lem4865669) (@lem4865668 A u f s t x)). Qed.
Lemma lem4865671 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term994 A u f s x t) = (term989 A u f s t x).
Proof. exact (TRANS (@lem4865670 A u f s t x) (@lem4865662 A u f s t x)). Qed.
Lemma lem4865672 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term995 A u f s x) = (term996 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865671 A u f s t x)). Qed.
Lemma lem4865673 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865674 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term992 A u f s x) = (term997 A u f s x).
Proof. exact (MK_COMB (@lem4865673 A) (@lem4865672 A u f s x)). Qed.
Lemma lem4865675 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term991 A u f s x) = (term997 A u f s x).
Proof. exact (TRANS (@lem4865667 A u f s x) (@lem4865674 A u f s x)). Qed.
Lemma lem4865676 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term950 A u f s x) = (term950 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865665 A u f s t x)). Qed.
Lemma lem4865677 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865678 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term951 A u f s x) = (term951 A u f s x).
Proof. exact (MK_COMB (@lem4865677 A) (@lem4865676 A u f s x)). Qed.
Lemma lem4865679 {A : Type'} (P : type686 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4865680 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term998 A u f x) = (term999 A u f x).
Proof. exact (@lem4865679 A (term952 A u f x)). Qed.
Lemma lem4865681 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1000 A u f x s) = (term951 A u f s x).
Proof. exact (eq_refl (term1000 A u f x s)). Qed.
Lemma lem4865682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4865683 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1001 A u f x s) = (term991 A u f s x).
Proof. exact (MK_COMB (@lem4865682) (@lem4865681 A u f s x)). Qed.
Lemma lem4865684 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1001 A u f x s) = (term997 A u f s x).
Proof. exact (TRANS (@lem4865683 A u f s x) (@lem4865675 A u f s x)). Qed.
Lemma lem4865685 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1002 A u f x) = (term1003 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865684 A u f s x)). Qed.
Lemma lem4865686 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865687 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term999 A u f x) = (term1004 A u f x).
Proof. exact (MK_COMB (@lem4865686 A) (@lem4865685 A u f x)). Qed.
Lemma lem4865688 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term998 A u f x) = (term1004 A u f x).
Proof. exact (TRANS (@lem4865680 A u f x) (@lem4865687 A u f x)). Qed.
Lemma lem4865689 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term952 A u f x) = (term952 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865678 A u f s x)). Qed.
Lemma lem4865690 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865691 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term953 A u f x) = (term953 A u f x).
Proof. exact (MK_COMB (@lem4865690 A) (@lem4865689 A u f x)). Qed.
Lemma lem4865700 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1005 A u t x) = (term1006 A u t x).
Proof. exact (@lem17045 (u t) (t x)). Qed.
Lemma lem4865703 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term956 A u t x) = (term956 A u t x).
Proof. exact (eq_refl (term956 A u t x)). Qed.
Lemma lem4865704 {A : Type'} (P : type686 A) : (term346 A P) = (term347 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4865705 {A : Type'} (u : type686 A) (x : A) : (term1007 A u x) = (term1008 A u x).
Proof. exact (@lem4865704 A (term958 A u x)). Qed.
Lemma lem4865706 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1009 A u x t) = (term956 A u t x).
Proof. exact (eq_refl (term1009 A u x t)). Qed.
Lemma lem4865707 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4865708 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1010 A u x t) = (term1005 A u t x).
Proof. exact (MK_COMB (@lem4865707) (@lem4865706 A u t x)). Qed.
Lemma lem4865709 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1010 A u x t) = (term1006 A u t x).
Proof. exact (TRANS (@lem4865708 A u t x) (@lem4865700 A u t x)). Qed.
Lemma lem4865710 {A : Type'} (u : type686 A) (x : A) : (term1011 A u x) = (term1012 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865709 A u t x)). Qed.
Lemma lem4865711 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4865712 {A : Type'} (u : type686 A) (x : A) : (term1008 A u x) = (term1013 A u x).
Proof. exact (MK_COMB (@lem4865711 A) (@lem4865710 A u x)). Qed.
Lemma lem4865713 {A : Type'} (u : type686 A) (x : A) : (term1007 A u x) = (term1013 A u x).
Proof. exact (TRANS (@lem4865705 A u x) (@lem4865712 A u x)). Qed.
Lemma lem4865714 {A : Type'} (u : type686 A) (x : A) : (term958 A u x) = (term958 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865703 A u t x)). Qed.
Lemma lem4865715 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865716 {A : Type'} (u : type686 A) (x : A) : (term959 A u x) = (term959 A u x).
Proof. exact (MK_COMB (@lem4865715 A) (@lem4865714 A u x)). Qed.
Lemma lem4865717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865718 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1014 A u f x) = (term1015 A u f x).
Proof. exact (MK_COMB (@lem4865717) (@lem4865688 A u f x)). Qed.
Lemma lem4865719 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1016 A f u x) = (term1017 A f u x).
Proof. exact (MK_COMB (@lem4865718 A u f x) (@lem4865716 A u x)). Qed.
Lemma lem4865720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865721 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1018 A u f x) = (term1018 A u f x).
Proof. exact (MK_COMB (@lem4865720) (@lem4865691 A u f x)). Qed.
Lemma lem4865722 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1019 A f u x) = (term1020 A f u x).
Proof. exact (MK_COMB (@lem4865721 A u f x) (@lem4865713 A u x)). Qed.
Lemma lem4865723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865724 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1021 A f u x) = (term1022 A f u x).
Proof. exact (MK_COMB (@lem4865723) (@lem4865722 A f u x)). Qed.
Lemma lem4865725 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1023 A f u x) = (term1024 A f u x).
Proof. exact (MK_COMB (@lem4865724 A f u x) (@lem4865719 A f u x)). Qed.
Lemma lem4865726 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term983 A f u x) = (term1023 A f u x).
Proof. exact (@lem17646 (term953 A u f x) (term959 A u x)). Qed.
Lemma lem4865727 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term983 A f u x) = (term1024 A f u x).
Proof. exact (TRANS (@lem4865726 A f u x) (@lem4865725 A f u x)). Qed.
Lemma lem4865910 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4865911 {A : Type'} (P : type686 A) (Q : Prop) : (term1025 A P Q) = (term1026 A P Q).
Proof. exact (@lem4865910 (A -> Prop) P Q). Qed.
Lemma lem4865912 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1027 A f u x) = (term1028 A f u x).
Proof. exact (@lem4865911 A (term952 A u f x) (term1013 A u x)). Qed.
Lemma lem4865913 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1000 A u f x s) = (term951 A u f s x).
Proof. exact (eq_refl (term1000 A u f x s)). Qed.
Lemma lem4865914 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1029 A u f x) = (term952 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865913 A u f s x)). Qed.
Lemma lem4865915 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865916 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1030 A u f x) = (term953 A u f x).
Proof. exact (MK_COMB (@lem4865915 A) (@lem4865914 A u f x)). Qed.
Lemma lem4865917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865918 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1031 A u f x) = (term1018 A u f x).
Proof. exact (MK_COMB (@lem4865917) (@lem4865916 A u f x)). Qed.
Lemma lem4865919 {A : Type'} (u : type686 A) (x : A) : (term1013 A u x) = (term1013 A u x).
Proof. exact (eq_refl (term1013 A u x)). Qed.
Lemma lem4865920 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1027 A f u x) = (term1020 A f u x).
Proof. exact (MK_COMB (@lem4865918 A u f x) (@lem4865919 A u x)). Qed.
Lemma lem4865921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865922 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1032 A f u x) = (term1033 A f u x).
Proof. exact (MK_COMB (@lem4865921) (@lem4865920 A f u x)). Qed.
Lemma lem4865923 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1000 A u f x s) = (term951 A u f s x).
Proof. exact (eq_refl (term1000 A u f x s)). Qed.
Lemma lem4865924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865925 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1034 A u f x s) = (term1035 A u f s x).
Proof. exact (MK_COMB (@lem4865924) (@lem4865923 A u f s x)). Qed.
Lemma lem4865926 {A : Type'} (u : type686 A) (x : A) : (term1013 A u x) = (term1013 A u x).
Proof. exact (eq_refl (term1013 A u x)). Qed.
Lemma lem4865927 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1036 A f s u x) = (term1037 A f s u x).
Proof. exact (MK_COMB (@lem4865925 A u f s x) (@lem4865926 A u x)). Qed.
Lemma lem4865928 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1038 A f u x) = (term1039 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865927 A f s u x)). Qed.
Lemma lem4865929 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865930 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1028 A f u x) = (term1040 A f u x).
Proof. exact (MK_COMB (@lem4865929 A) (@lem4865928 A f u x)). Qed.
Lemma lem4865931 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1027 A f u x) = (term1028 A f u x)) = ((term1020 A f u x) = (term1040 A f u x)).
Proof. exact (MK_COMB (@lem4865922 A f u x) (@lem4865930 A f u x)). Qed.
Lemma lem4865932 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1020 A f u x) = (term1040 A f u x).
Proof. exact (EQ_MP (@lem4865931 A f u x) (@lem4865912 A f u x)). Qed.
Lemma lem4865934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term451 A P Q) = (term452 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4865935 {A : Type'} (P : type686 A) (Q : Prop) : (term1025 A P Q) = (term1026 A P Q).
Proof. exact (@lem4865934 (A -> Prop) P Q). Qed.
Lemma lem4865936 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1041 A f s u x) = (term1042 A f s u x).
Proof. exact (@lem4865935 A (term950 A u f s x) (term1013 A u x)). Qed.
Lemma lem4865937 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term993 A u f s x t) = (term949 A u f s t x).
Proof. exact (eq_refl (term993 A u f s x t)). Qed.
Lemma lem4865938 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1043 A u f s x) = (term950 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865937 A u f s t x)). Qed.
Lemma lem4865939 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865940 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1044 A u f s x) = (term951 A u f s x).
Proof. exact (MK_COMB (@lem4865939 A) (@lem4865938 A u f s x)). Qed.
Lemma lem4865941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865942 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1045 A u f s x) = (term1035 A u f s x).
Proof. exact (MK_COMB (@lem4865941) (@lem4865940 A u f s x)). Qed.
Lemma lem4865943 {A : Type'} (u : type686 A) (x : A) : (term1013 A u x) = (term1013 A u x).
Proof. exact (eq_refl (term1013 A u x)). Qed.
Lemma lem4865944 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1041 A f s u x) = (term1037 A f s u x).
Proof. exact (MK_COMB (@lem4865942 A u f s x) (@lem4865943 A u x)). Qed.
Lemma lem4865945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865946 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1046 A f s u x) = (term1047 A f s u x).
Proof. exact (MK_COMB (@lem4865945) (@lem4865944 A f s u x)). Qed.
Lemma lem4865947 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term993 A u f s x t) = (term949 A u f s t x).
Proof. exact (eq_refl (term993 A u f s x t)). Qed.
Lemma lem4865948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4865949 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1048 A u f s x t) = (term1049 A u f s t x).
Proof. exact (MK_COMB (@lem4865948) (@lem4865947 A u f s t x)). Qed.
Lemma lem4865950 {A : Type'} (u : type686 A) (x : A) : (term1013 A u x) = (term1013 A u x).
Proof. exact (eq_refl (term1013 A u x)). Qed.
Lemma lem4865951 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1050 A f s t u x) = (term1051 A f s t u x).
Proof. exact (MK_COMB (@lem4865949 A u f s t x) (@lem4865950 A u x)). Qed.
Lemma lem4865952 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1052 A f s u x) = (term1053 A f s u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865951 A f s t u x)). Qed.
Lemma lem4865953 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865954 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1042 A f s u x) = (term1054 A f s u x).
Proof. exact (MK_COMB (@lem4865953 A) (@lem4865952 A f s u x)). Qed.
Lemma lem4865955 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : ((term1041 A f s u x) = (term1042 A f s u x)) = ((term1037 A f s u x) = (term1054 A f s u x)).
Proof. exact (MK_COMB (@lem4865946 A f s u x) (@lem4865954 A f s u x)). Qed.
Lemma lem4865956 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1037 A f s u x) = (term1054 A f s u x).
Proof. exact (EQ_MP (@lem4865955 A f s u x) (@lem4865936 A f s u x)). Qed.
Lemma lem4865957 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1039 A f u x) = (term1055 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865956 A f s u x)). Qed.
Lemma lem4865958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865959 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1040 A f u x) = (term1056 A f u x).
Proof. exact (MK_COMB (@lem4865958 A) (@lem4865957 A f u x)). Qed.
Lemma lem4865960 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1020 A f u x) = (term1056 A f u x).
Proof. exact (TRANS (@lem4865932 A f u x) (@lem4865959 A f u x)). Qed.
Lemma lem4865961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865962 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1022 A f u x) = (term1057 A f u x).
Proof. exact (MK_COMB (@lem4865961) (@lem4865960 A f u x)). Qed.
Lemma lem4865964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term471 A P Q) = (term472 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4865965 {A : Type'} (P : Prop) (Q : type686 A) : (term1058 A P Q) = (term1059 A P Q).
Proof. exact (@lem4865964 (A -> Prop) P Q). Qed.
Lemma lem4865966 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1060 A f u x) = (term1061 A f u x).
Proof. exact (@lem4865965 A (term1004 A u f x) (term958 A u x)). Qed.
Lemma lem4865967 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1009 A u x t) = (term956 A u t x).
Proof. exact (eq_refl (term1009 A u x t)). Qed.
Lemma lem4865968 {A : Type'} (u : type686 A) (x : A) : (term1062 A u x) = (term958 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865967 A u t x)). Qed.
Lemma lem4865969 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865970 {A : Type'} (u : type686 A) (x : A) : (term1063 A u x) = (term959 A u x).
Proof. exact (MK_COMB (@lem4865969 A) (@lem4865968 A u x)). Qed.
Lemma lem4865971 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1015 A u f x) = (term1015 A u f x).
Proof. exact (eq_refl (term1015 A u f x)). Qed.
Lemma lem4865972 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1060 A f u x) = (term1017 A f u x).
Proof. exact (MK_COMB (@lem4865971 A u f x) (@lem4865970 A u x)). Qed.
Lemma lem4865973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4865974 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1064 A f u x) = (term1065 A f u x).
Proof. exact (MK_COMB (@lem4865973) (@lem4865972 A f u x)). Qed.
Lemma lem4865975 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1009 A u x t) = (term956 A u t x).
Proof. exact (eq_refl (term1009 A u x t)). Qed.
Lemma lem4865976 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1015 A u f x) = (term1015 A u f x).
Proof. exact (eq_refl (term1015 A u f x)). Qed.
Lemma lem4865977 {A : Type'} (f : type639 A) (u : type686 A) (t : A -> Prop) (x : A) : (term1066 A f u x t) = (term1067 A f u t x).
Proof. exact (MK_COMB (@lem4865976 A u f x) (@lem4865975 A u t x)). Qed.
Lemma lem4865978 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1068 A f u x) = (term1069 A f u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4865977 A f u t x)). Qed.
Lemma lem4865979 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865980 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1061 A f u x) = (term1070 A f u x).
Proof. exact (MK_COMB (@lem4865979 A) (@lem4865978 A f u x)). Qed.
Lemma lem4865981 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1060 A f u x) = (term1061 A f u x)) = ((term1017 A f u x) = (term1070 A f u x)).
Proof. exact (MK_COMB (@lem4865974 A f u x) (@lem4865980 A f u x)). Qed.
Lemma lem4865982 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1017 A f u x) = (term1070 A f u x).
Proof. exact (EQ_MP (@lem4865981 A f u x) (@lem4865966 A f u x)). Qed.
Lemma lem4865983 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1024 A f u x) = (term1071 A f u x).
Proof. exact (MK_COMB (@lem4865962 A f u x) (@lem4865982 A f u x)). Qed.
Lemma lem4865985 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term1072 A P Q) = (term1073 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4865986 {A : Type'} (P : type686 A) (Q : type686 A) : (term1074 A P Q) = (term1075 A P Q).
Proof. exact (@lem4865985 (A -> Prop) P Q). Qed.
Lemma lem4865987 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1076 A f u x) = (term1077 A f u x).
Proof. exact (@lem4865986 A (term1055 A f u x) (term1069 A f u x)). Qed.
Lemma lem4865988 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1078 A f u x s) = (term1054 A f s u x).
Proof. exact (eq_refl (term1078 A f u x s)). Qed.
Lemma lem4865989 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1079 A f u x) = (term1055 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865988 A f s u x)). Qed.
Lemma lem4865990 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865991 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1080 A f u x) = (term1056 A f u x).
Proof. exact (MK_COMB (@lem4865990 A) (@lem4865989 A f u x)). Qed.
Lemma lem4865992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4865993 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1081 A f u x) = (term1057 A f u x).
Proof. exact (MK_COMB (@lem4865992) (@lem4865991 A f u x)). Qed.
Lemma lem4865994 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1082 A f u x s) = (term1067 A f u s x).
Proof. exact (eq_refl (term1082 A f u x s)). Qed.
Lemma lem4865995 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1083 A f u x) = (term1069 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4865994 A f u s x)). Qed.
Lemma lem4865996 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4865997 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1084 A f u x) = (term1070 A f u x).
Proof. exact (MK_COMB (@lem4865996 A) (@lem4865995 A f u x)). Qed.
Lemma lem4865998 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1076 A f u x) = (term1071 A f u x).
Proof. exact (MK_COMB (@lem4865993 A f u x) (@lem4865997 A f u x)). Qed.
Lemma lem4865999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866000 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1085 A f u x) = (term1086 A f u x).
Proof. exact (MK_COMB (@lem4865999) (@lem4865998 A f u x)). Qed.
Lemma lem4866001 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1078 A f u x s) = (term1054 A f s u x).
Proof. exact (eq_refl (term1078 A f u x s)). Qed.
Lemma lem4866002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866003 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1087 A f u x s) = (term1088 A f s u x).
Proof. exact (MK_COMB (@lem4866002) (@lem4866001 A f s u x)). Qed.
Lemma lem4866004 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1082 A f u x s) = (term1067 A f u s x).
Proof. exact (eq_refl (term1082 A f u x s)). Qed.
Lemma lem4866005 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1089 A f u x s) = (term1090 A f u s x).
Proof. exact (MK_COMB (@lem4866003 A f s u x) (@lem4866004 A f u s x)). Qed.
Lemma lem4866006 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1091 A f u x) = (term1092 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4866005 A f u s x)). Qed.
Lemma lem4866007 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4866008 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1077 A f u x) = (term1093 A f u x).
Proof. exact (MK_COMB (@lem4866007 A) (@lem4866006 A f u x)). Qed.
Lemma lem4866009 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1076 A f u x) = (term1077 A f u x)) = ((term1071 A f u x) = (term1093 A f u x)).
Proof. exact (MK_COMB (@lem4866000 A f u x) (@lem4866008 A f u x)). Qed.
Lemma lem4866010 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1071 A f u x) = (term1093 A f u x).
Proof. exact (EQ_MP (@lem4866009 A f u x) (@lem4865987 A f u x)). Qed.
Lemma lem4866013 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1094 A f u x) = (term1094 A f u x).
Proof. exact (eq_refl (term1094 A f u x)). Qed.
Lemma lem4866014 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1094 A f u x) = ((term1071 A f u x) = (term1093 A f u x)).
Proof. exact (eq_refl (term1094 A f u x)). Qed.
Lemma lem4866015 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1095 A f u x) = (term1095 A f u x).
Proof. exact (eq_refl (term1095 A f u x)). Qed.
Lemma lem4866016 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1094 A f u x) = (term1094 A f u x)) = ((term1094 A f u x) = ((term1071 A f u x) = (term1093 A f u x))).
Proof. exact (MK_COMB (@lem4866015 A f u x) (@lem4866014 A f u x)). Qed.
Lemma lem4866017 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1094 A f u x) = ((term1071 A f u x) = (term1093 A f u x)).
Proof. exact (eq_refl (term1094 A f u x)). Qed.
Lemma lem4866018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866019 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1095 A f u x) = (term1096 A f u x).
Proof. exact (MK_COMB (@lem4866018) (@lem4866017 A f u x)). Qed.
Lemma lem4866020 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1071 A f u x) = (term1093 A f u x)) = ((term1071 A f u x) = (term1093 A f u x)).
Proof. exact (eq_refl ((term1071 A f u x) = (term1093 A f u x))). Qed.
Lemma lem4866021 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1094 A f u x) = ((term1071 A f u x) = (term1093 A f u x))) = (((term1071 A f u x) = (term1093 A f u x)) = ((term1071 A f u x) = (term1093 A f u x))).
Proof. exact (MK_COMB (@lem4866019 A f u x) (@lem4866020 A f u x)). Qed.
Lemma lem4866022 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1094 A f u x) = (term1094 A f u x)) = (((term1071 A f u x) = (term1093 A f u x)) = ((term1071 A f u x) = (term1093 A f u x))).
Proof. exact (TRANS (@lem4866016 A f u x) (@lem4866021 A f u x)). Qed.
Lemma lem4866023 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : ((term1071 A f u x) = (term1093 A f u x)) = ((term1071 A f u x) = (term1093 A f u x)).
Proof. exact (EQ_MP (@lem4866022 A f u x) (@lem4866013 A f u x)). Qed.
Lemma lem4866024 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1071 A f u x) = (term1093 A f u x).
Proof. exact (EQ_MP (@lem4866023 A f u x) (@lem4866010 A f u x)). Qed.
Lemma lem4866026 {A : Type'} (P : A -> Prop) (Q : Prop) : (term406 A P Q) = (term407 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4866027 {A : Type'} (P : type686 A) (Q : Prop) : (term408 A P Q) = (term409 A P Q).
Proof. exact (@lem4866026 (A -> Prop) P Q). Qed.
Lemma lem4866028 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1097 A f u s x) = (term1098 A f u s x).
Proof. exact (@lem4866027 A (term1053 A f s u x) (term1067 A f u s x)). Qed.
Lemma lem4866029 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1099 A f s u x t) = (term1051 A f s t u x).
Proof. exact (eq_refl (term1099 A f s u x t)). Qed.
Lemma lem4866030 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1100 A f s u x) = (term1053 A f s u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866029 A f s t u x)). Qed.
Lemma lem4866031 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4866032 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1101 A f s u x) = (term1054 A f s u x).
Proof. exact (MK_COMB (@lem4866031 A) (@lem4866030 A f s u x)). Qed.
Lemma lem4866033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866034 {A : Type'} (f : type639 A) (s : A -> Prop) (u : type686 A) (x : A) : (term1102 A f s u x) = (term1088 A f s u x).
Proof. exact (MK_COMB (@lem4866033) (@lem4866032 A f s u x)). Qed.
Lemma lem4866035 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1067 A f u s x) = (term1067 A f u s x).
Proof. exact (eq_refl (term1067 A f u s x)). Qed.
Lemma lem4866036 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1097 A f u s x) = (term1090 A f u s x).
Proof. exact (MK_COMB (@lem4866034 A f s u x) (@lem4866035 A f u s x)). Qed.
Lemma lem4866037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866038 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1103 A f u s x) = (term1104 A f u s x).
Proof. exact (MK_COMB (@lem4866037) (@lem4866036 A f u s x)). Qed.
Lemma lem4866039 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1099 A f s u x t) = (term1051 A f s t u x).
Proof. exact (eq_refl (term1099 A f s u x t)). Qed.
Lemma lem4866040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866041 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1105 A f s u x t) = (term1106 A f s t u x).
Proof. exact (MK_COMB (@lem4866040) (@lem4866039 A f s t u x)). Qed.
Lemma lem4866042 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1067 A f u s x) = (term1067 A f u s x).
Proof. exact (eq_refl (term1067 A f u s x)). Qed.
Lemma lem4866043 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1107 A t f u s x) = (term1108 A t f u s x).
Proof. exact (MK_COMB (@lem4866041 A f s t u x) (@lem4866042 A f u s x)). Qed.
Lemma lem4866044 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1109 A f u s x) = (term1110 A f u s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866043 A t f u s x)). Qed.
Lemma lem4866045 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4866046 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1098 A f u s x) = (term1111 A f u s x).
Proof. exact (MK_COMB (@lem4866045 A) (@lem4866044 A f u s x)). Qed.
Lemma lem4866047 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : ((term1097 A f u s x) = (term1098 A f u s x)) = ((term1090 A f u s x) = (term1111 A f u s x)).
Proof. exact (MK_COMB (@lem4866038 A f u s x) (@lem4866046 A f u s x)). Qed.
Lemma lem4866048 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1090 A f u s x) = (term1111 A f u s x).
Proof. exact (EQ_MP (@lem4866047 A f u s x) (@lem4866028 A f u s x)). Qed.
Lemma lem4866049 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1092 A f u x) = (term1112 A f u x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4866048 A f u s x)). Qed.
Lemma lem4866050 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4866051 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1093 A f u x) = (term1113 A f u x).
Proof. exact (MK_COMB (@lem4866050 A) (@lem4866049 A f u x)). Qed.
Lemma lem4866052 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1071 A f u x) = (term1113 A f u x).
Proof. exact (TRANS (@lem4866024 A f u x) (@lem4866051 A f u x)). Qed.
Lemma lem4866054 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term1024 A f u x) = (term1113 A f u x).
Proof. exact (TRANS (@lem4865983 A f u x) (@lem4866052 A f u x)). Qed.
Lemma lem4866055 {A : Type'} (f : type639 A) (u : type686 A) (x : A) : (term983 A f u x) = (term1113 A f u x).
Proof. exact (TRANS (@lem4865727 A f u x) (@lem4866054 A f u x)). Qed.
Lemma lem4866056 {A : Type'} (f : type639 A) (u : type686 A) (x : A) (h1 : term983 A f u x) : term1113 A f u x.
Proof. exact (EQ_MP (@lem4866055 A f u x) (@lem4865006 A f u x h1)). Qed.
Lemma lem4866057 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1111 A f u s x) : term1111 A f u s x.
Proof. exact (h1). Qed.
Lemma lem4866058 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1108 A t f u s x) : term1108 A t f u s x.
Proof. exact (h1). Qed.
Lemma lem4866059 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term558 A P t' f u.
Proof. exact (h1). Qed.
Lemma lem4866064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866065 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866064 A Prop f x). Qed.
Lemma lem4866067 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4866065 A s x). Qed.
Lemma lem4866072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866073 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866072 (A -> Prop) Prop f x). Qed.
Lemma lem4866075 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4866073 A u s). Qed.
Lemma lem4866076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866077 {A : Type'} (u : type686 A) (s : A -> Prop) : (term310 A u s) = (term563 A u s).
Proof. exact (MK_COMB (@lem4866076) (@lem4866075 A u s)). Qed.
Lemma lem4866078 {A : Type'} (u : type686 A) (s : A -> Prop) (x : A) : (term956 A u s x) = (term1114 A u s x).
Proof. exact (MK_COMB (@lem4866077 A u s) (@lem4866067 A s x)). Qed.
Lemma lem4866079 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866085 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866084 A Prop f x). Qed.
Lemma lem4866087 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4866085 A t x). Qed.
Lemma lem4866088 {A : Type'} (t : A -> Prop) (x : A) : (term355 A t x) = (term566 A t x).
Proof. exact (MK_COMB (@lem4866079) (@lem4866087 A t x)). Qed.
Lemma lem4866089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866097 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866096 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866098 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4866097 A f s). Qed.
Lemma lem4866099 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4866100 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4866098 A f s) (@lem4866099 A t)). Qed.
Lemma lem4866102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866103 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866102 (A -> Prop) Prop f x). Qed.
Lemma lem4866104 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term562 A f s t).
Proof. exact (@lem4866103 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4866106 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term562 A f s t).
Proof. exact (TRANS (@lem4866100 A f s t) (@lem4866104 A f s t)). Qed.
Lemma lem4866107 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term567 A f s t) = (term568 A f s t).
Proof. exact (MK_COMB (@lem4866089) (@lem4866106 A f s t)). Qed.
Lemma lem4866108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866113 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866114 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866113 (A -> Prop) Prop f x). Qed.
Lemma lem4866116 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4866114 A u s). Qed.
Lemma lem4866117 {A : Type'} (u : type686 A) (s : A -> Prop) : (term340 A u s) = (term565 A u s).
Proof. exact (MK_COMB (@lem4866108) (@lem4866116 A u s)). Qed.
Lemma lem4866118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866119 {A : Type'} (u : type686 A) (s : A -> Prop) : (term370 A u s) = (term612 A u s).
Proof. exact (MK_COMB (@lem4866118) (@lem4866117 A u s)). Qed.
Lemma lem4866120 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term985 A u f s t) = (term859 A u f s t).
Proof. exact (MK_COMB (@lem4866119 A u s) (@lem4866107 A f s t)). Qed.
Lemma lem4866121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866122 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term987 A u f s t) = (term1115 A u f s t).
Proof. exact (MK_COMB (@lem4866121) (@lem4866120 A u f s t)). Qed.
Lemma lem4866123 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term989 A u f s t x) = (term1116 A u f s t x).
Proof. exact (MK_COMB (@lem4866122 A u f s t) (@lem4866088 A t x)). Qed.
Lemma lem4866124 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term996 A u f s x) = (term1117 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866123 A u f s t x)). Qed.
Lemma lem4866125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866126 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term997 A u f s x) = (term1118 A u f s x).
Proof. exact (MK_COMB (@lem4866125 A) (@lem4866124 A u f s x)). Qed.
Lemma lem4866127 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1003 A u f x) = (term1119 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4866126 A u f s x)). Qed.
Lemma lem4866128 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866129 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1004 A u f x) = (term1120 A u f x).
Proof. exact (MK_COMB (@lem4866128 A) (@lem4866127 A u f x)). Qed.
Lemma lem4866130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866131 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1015 A u f x) = (term1121 A u f x).
Proof. exact (MK_COMB (@lem4866130) (@lem4866129 A u f x)). Qed.
Lemma lem4866132 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1067 A f u s x) = (term1122 A f u s x).
Proof. exact (MK_COMB (@lem4866131 A u f x) (@lem4866078 A u s x)). Qed.
Lemma lem4866133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866138 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866139 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866138 A Prop f x). Qed.
Lemma lem4866141 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4866139 A t x). Qed.
Lemma lem4866142 {A : Type'} (t : A -> Prop) (x : A) : (term355 A t x) = (term566 A t x).
Proof. exact (MK_COMB (@lem4866133) (@lem4866141 A t x)). Qed.
Lemma lem4866143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866149 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866148 (A -> Prop) Prop f x). Qed.
Lemma lem4866151 {A : Type'} (u : type686 A) (t : A -> Prop) : (u t) = (@I ((A -> Prop) -> Prop) u t).
Proof. exact (@lem4866149 A u t). Qed.
Lemma lem4866152 {A : Type'} (u : type686 A) (t : A -> Prop) : (term340 A u t) = (term565 A u t).
Proof. exact (MK_COMB (@lem4866143) (@lem4866151 A u t)). Qed.
Lemma lem4866153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866154 {A : Type'} (u : type686 A) (t : A -> Prop) : (term370 A u t) = (term612 A u t).
Proof. exact (MK_COMB (@lem4866153) (@lem4866152 A u t)). Qed.
Lemma lem4866155 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1006 A u t x) = (term1123 A u t x).
Proof. exact (MK_COMB (@lem4866154 A u t) (@lem4866142 A t x)). Qed.
Lemma lem4866156 {A : Type'} (u : type686 A) (x : A) : (term1012 A u x) = (term1124 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866155 A u t x)). Qed.
Lemma lem4866157 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866158 {A : Type'} (u : type686 A) (x : A) : (term1013 A u x) = (term1125 A u x).
Proof. exact (MK_COMB (@lem4866157 A) (@lem4866156 A u x)). Qed.
Lemma lem4866163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866164 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866163 A Prop f x). Qed.
Lemma lem4866166 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4866164 A t x). Qed.
Lemma lem4866173 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866174 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866173 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866175 {A : Type'} (f : type639 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s).
Proof. exact (@lem4866174 A f s). Qed.
Lemma lem4866176 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4866177 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t).
Proof. exact (MK_COMB (@lem4866175 A f s) (@lem4866176 A t)). Qed.
Lemma lem4866179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866180 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866179 (A -> Prop) Prop f x). Qed.
Lemma lem4866181 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s t) = (term562 A f s t).
Proof. exact (@lem4866180 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f s) t). Qed.
Lemma lem4866183 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (f s t) = (term562 A f s t).
Proof. exact (TRANS (@lem4866177 A f s t) (@lem4866181 A f s t)). Qed.
Lemma lem4866188 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866189 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866188 (A -> Prop) Prop f x). Qed.
Lemma lem4866191 {A : Type'} (u : type686 A) (s : A -> Prop) : (u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4866189 A u s). Qed.
Lemma lem4866192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866193 {A : Type'} (u : type686 A) (s : A -> Prop) : (term310 A u s) = (term563 A u s).
Proof. exact (MK_COMB (@lem4866192) (@lem4866191 A u s)). Qed.
Lemma lem4866194 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term311 A u f s t) = (term564 A u f s t).
Proof. exact (MK_COMB (@lem4866193 A u s) (@lem4866183 A f s t)). Qed.
Lemma lem4866195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866196 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term948 A u f s t) = (term1126 A u f s t).
Proof. exact (MK_COMB (@lem4866195) (@lem4866194 A u f s t)). Qed.
Lemma lem4866197 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term949 A u f s t x) = (term1127 A u f s t x).
Proof. exact (MK_COMB (@lem4866196 A u f s t) (@lem4866166 A t x)). Qed.
Lemma lem4866198 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866199 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1049 A u f s t x) = (term1128 A u f s t x).
Proof. exact (MK_COMB (@lem4866198) (@lem4866197 A u f s t x)). Qed.
Lemma lem4866200 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1051 A f s t u x) = (term1129 A f s t u x).
Proof. exact (MK_COMB (@lem4866199 A u f s t x) (@lem4866158 A u x)). Qed.
Lemma lem4866201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866202 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) : (term1106 A f s t u x) = (term1130 A f s t u x).
Proof. exact (MK_COMB (@lem4866201) (@lem4866200 A f s t u x)). Qed.
Lemma lem4866203 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) : (term1108 A t f u s x) = (term1131 A t f u s x).
Proof. exact (MK_COMB (@lem4866202 A f s t u x) (@lem4866132 A f u s x)). Qed.
Lemma lem4866204 {A : Type'} (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1108 A t f u s x) : term1131 A t f u s x.
Proof. exact (EQ_MP (@lem4866203 A t f u s x) (@lem4866058 A t f u s x h1)). Qed.
Lemma lem4866209 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866210 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4866209 (type686 A) Prop f x). Qed.
Lemma lem4866212 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = (@I (((A -> Prop) -> Prop) -> Prop) (@ARBITRARY A) u).
Proof. exact (@lem4866210 A (@ARBITRARY A) u). Qed.
Lemma lem4866217 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866218 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866217 A Prop f x). Qed.
Lemma lem4866220 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4866218 A c x). Qed.
Lemma lem4866221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866227 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866226 A Prop f x). Qed.
Lemma lem4866229 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4866227 A t x). Qed.
Lemma lem4866230 {A : Type'} (t : A -> Prop) (x : A) : (term355 A t x) = (term566 A t x).
Proof. exact (MK_COMB (@lem4866221) (@lem4866229 A t x)). Qed.
Lemma lem4866231 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866238 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866239 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866238 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866240 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4866239 A f c). Qed.
Lemma lem4866241 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4866242 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t).
Proof. exact (MK_COMB (@lem4866240 A f c) (@lem4866241 A t)). Qed.
Lemma lem4866244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866245 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866244 (A -> Prop) Prop f x). Qed.
Lemma lem4866246 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c t) = (term562 A f c t).
Proof. exact (@lem4866245 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) t). Qed.
Lemma lem4866248 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (f c t) = (term562 A f c t).
Proof. exact (TRANS (@lem4866242 A f c t) (@lem4866246 A f c t)). Qed.
Lemma lem4866249 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term567 A f c t) = (term568 A f c t).
Proof. exact (MK_COMB (@lem4866231) (@lem4866248 A f c t)). Qed.
Lemma lem4866250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866251 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) : (term569 A f c t) = (term570 A f c t).
Proof. exact (MK_COMB (@lem4866250) (@lem4866249 A f c t)). Qed.
Lemma lem4866252 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term345 A f c t x) = (term571 A f c t x).
Proof. exact (MK_COMB (@lem4866251 A f c t) (@lem4866230 A t x)). Qed.
Lemma lem4866253 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term353 A f c x) = (term572 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866252 A f c t x)). Qed.
Lemma lem4866254 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866255 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term354 A f c x) = (term573 A f c x).
Proof. exact (MK_COMB (@lem4866254 A) (@lem4866253 A f c x)). Qed.
Lemma lem4866256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866257 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term357 A f c x) = (term574 A f c x).
Proof. exact (MK_COMB (@lem4866256) (@lem4866255 A f c x)). Qed.
Lemma lem4866258 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term359 A f c x) = (term575 A f c x).
Proof. exact (MK_COMB (@lem4866257 A f c x) (@lem4866220 A c x)). Qed.
Lemma lem4866259 {A : Type'} (f : type639 A) (c : A -> Prop) : (term382 A f c) = (term576 A f c).
Proof. exact (fun_ext (fun x : A => @lem4866258 A f c x)). Qed.
Lemma lem4866260 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866261 {A : Type'} (f : type639 A) (c : A -> Prop) : (term397 A f c) = (term577 A f c).
Proof. exact (MK_COMB (@lem4866260 A) (@lem4866259 A f c)). Qed.
Lemma lem4866262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866268 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866267 A Prop f x). Qed.
Lemma lem4866270 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4866268 A c x). Qed.
Lemma lem4866271 {A : Type'} (c : A -> Prop) (x : A) : (term355 A c x) = (term566 A c x).
Proof. exact (MK_COMB (@lem4866262) (@lem4866270 A c x)). Qed.
Lemma lem4866280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866281 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4866280 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4866282 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4866281 A t' c). Qed.
Lemma lem4866283 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4866284 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4866282 A t' c) (@lem4866283 A x)). Qed.
Lemma lem4866286 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866287 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4866286 A (A -> Prop) f x). Qed.
Lemma lem4866288 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term578 A t' c x).
Proof. exact (@lem4866287 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4866289 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term578 A t' c x).
Proof. exact (TRANS (@lem4866284 A t' c x) (@lem4866288 A t' c x)). Qed.
Lemma lem4866290 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4866291 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term579 A t' c x).
Proof. exact (MK_COMB (@lem4866289 A t' c x) (@lem4866290 A x)). Qed.
Lemma lem4866293 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866294 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4866293 A Prop f x). Qed.
Lemma lem4866295 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term579 A t' c x) = (term580 A t' c x).
Proof. exact (@lem4866294 A (term578 A t' c x) x). Qed.
Lemma lem4866297 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x x) = (term580 A t' c x).
Proof. exact (TRANS (@lem4866291 A t' c x) (@lem4866295 A t' c x)). Qed.
Lemma lem4866306 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866307 {A : Type'} (f : type667 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> A -> Prop) f x).
Proof. exact (@lem4866306 (A -> Prop) (type1402 A) f x). Qed.
Lemma lem4866308 {A : Type'} (t' : type667 A) (c : A -> Prop) : (t' c) = (@I ((A -> Prop) -> A -> A -> Prop) t' c).
Proof. exact (@lem4866307 A t' c). Qed.
Lemma lem4866309 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4866310 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (@I ((A -> Prop) -> A -> A -> Prop) t' c x).
Proof. exact (MK_COMB (@lem4866308 A t' c) (@lem4866309 A x)). Qed.
Lemma lem4866312 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866313 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4866312 A (A -> Prop) f x). Qed.
Lemma lem4866314 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (@I ((A -> Prop) -> A -> A -> Prop) t' c x) = (term578 A t' c x).
Proof. exact (@lem4866313 A (@I ((A -> Prop) -> A -> A -> Prop) t' c) x). Qed.
Lemma lem4866316 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (t' c x) = (term578 A t' c x).
Proof. exact (TRANS (@lem4866310 A t' c x) (@lem4866314 A t' c x)). Qed.
Lemma lem4866317 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (f c).
Proof. exact (eq_refl (f c)). Qed.
Lemma lem4866318 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term581 A f t' c x) = (term582 A f t' c x).
Proof. exact (MK_COMB (@lem4866317 A f c) (@lem4866316 A t' c x)). Qed.
Lemma lem4866320 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866321 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866320 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866322 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4866321 A f c). Qed.
Lemma lem4866323 {A : Type'} (t' : type667 A) (c : A -> Prop) (x : A) : (term578 A t' c x) = (term578 A t' c x).
Proof. exact (eq_refl (term578 A t' c x)). Qed.
Lemma lem4866324 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term582 A f t' c x) = (term583 A f t' c x).
Proof. exact (MK_COMB (@lem4866322 A f c) (@lem4866323 A t' c x)). Qed.
Lemma lem4866326 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866327 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866326 (A -> Prop) Prop f x). Qed.
Lemma lem4866328 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term583 A f t' c x) = (term584 A f t' c x).
Proof. exact (@lem4866327 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) (term578 A t' c x)). Qed.
Lemma lem4866329 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term582 A f t' c x) = (term584 A f t' c x).
Proof. exact (TRANS (@lem4866324 A f t' c x) (@lem4866328 A f t' c x)). Qed.
Lemma lem4866330 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term581 A f t' c x) = (term584 A f t' c x).
Proof. exact (TRANS (@lem4866318 A f t' c x) (@lem4866329 A f t' c x)). Qed.
Lemma lem4866331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866332 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term585 A f t' c x) = (term586 A f t' c x).
Proof. exact (MK_COMB (@lem4866331) (@lem4866330 A f t' c x)). Qed.
Lemma lem4866333 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term587 A f t' c x) = (term588 A f t' c x).
Proof. exact (MK_COMB (@lem4866332 A f t' c x) (@lem4866297 A t' c x)). Qed.
Lemma lem4866334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866335 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term589 A f t' c x) = (term590 A f t' c x).
Proof. exact (MK_COMB (@lem4866334) (@lem4866333 A f t' c x)). Qed.
Lemma lem4866336 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term591 A f t' c x) = (term592 A f t' c x).
Proof. exact (MK_COMB (@lem4866335 A f t' c x) (@lem4866271 A c x)). Qed.
Lemma lem4866337 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term593 A f t' c) = (term594 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4866336 A f t' c x)). Qed.
Lemma lem4866338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866339 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term595 A f t' c) = (term596 A f t' c).
Proof. exact (MK_COMB (@lem4866338 A) (@lem4866337 A f t' c)). Qed.
Lemma lem4866340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866341 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term597 A f t' c) = (term598 A f t' c).
Proof. exact (MK_COMB (@lem4866340) (@lem4866339 A f t' c)). Qed.
Lemma lem4866342 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term599 A t' f c) = (term600 A t' f c).
Proof. exact (MK_COMB (@lem4866341 A f t' c) (@lem4866261 A f c)). Qed.
Lemma lem4866347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866348 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866347 (A -> Prop) Prop f x). Qed.
Lemma lem4866350 {A : Type'} (P : type686 A) (c' : A -> Prop) : (P c') = (@I ((A -> Prop) -> Prop) P c').
Proof. exact (@lem4866348 A P c'). Qed.
Lemma lem4866351 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866358 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866359 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866358 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866360 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4866359 A f c). Qed.
Lemma lem4866361 {A : Type'} (c' : A -> Prop) : c' = c'.
Proof. exact (eq_refl c'). Qed.
Lemma lem4866362 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c').
Proof. exact (MK_COMB (@lem4866360 A f c) (@lem4866361 A c')). Qed.
Lemma lem4866364 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866365 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866364 (A -> Prop) Prop f x). Qed.
Lemma lem4866366 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c c') = (term562 A f c c').
Proof. exact (@lem4866365 A (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c) c'). Qed.
Lemma lem4866368 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (f c c') = (term562 A f c c').
Proof. exact (TRANS (@lem4866362 A f c c') (@lem4866366 A f c c')). Qed.
Lemma lem4866369 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term567 A f c c') = (term568 A f c c').
Proof. exact (MK_COMB (@lem4866351) (@lem4866368 A f c c')). Qed.
Lemma lem4866370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866371 {A : Type'} (f : type639 A) (c : A -> Prop) (c' : A -> Prop) : (term569 A f c c') = (term570 A f c c').
Proof. exact (MK_COMB (@lem4866370) (@lem4866369 A f c c')). Qed.
Lemma lem4866372 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term341 A f c P c') = (term601 A f c P c').
Proof. exact (MK_COMB (@lem4866371 A f c c') (@lem4866350 A P c')). Qed.
Lemma lem4866373 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term342 A f c P) = (term602 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866372 A f c P c')). Qed.
Lemma lem4866374 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866375 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term343 A f c P) = (term603 A f c P).
Proof. exact (MK_COMB (@lem4866374 A) (@lem4866373 A f c P)). Qed.
Lemma lem4866376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866377 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term367 A f c P) = (term604 A f c P).
Proof. exact (MK_COMB (@lem4866376) (@lem4866375 A f c P)). Qed.
Lemma lem4866378 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term605 A P t' f c) = (term606 A P t' f c).
Proof. exact (MK_COMB (@lem4866377 A f c P) (@lem4866342 A t' f c)). Qed.
Lemma lem4866379 {A : Type'} : (@ARBITRARY A) = (@ARBITRARY A).
Proof. exact (eq_refl (@ARBITRARY A)). Qed.
Lemma lem4866384 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866385 {A : Type'} (f : type639 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4866384 (A -> Prop) (type686 A) f x). Qed.
Lemma lem4866387 {A : Type'} (f : type639 A) (c : A -> Prop) : (f c) = (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c).
Proof. exact (@lem4866385 A f c). Qed.
Lemma lem4866388 {A : Type'} (f : type639 A) (c : A -> Prop) : (term490 A f c) = (term607 A f c).
Proof. exact (MK_COMB (@lem4866379 A) (@lem4866387 A f c)). Qed.
Lemma lem4866390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866391 {A : Type'} (f : type180 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> Prop) f x).
Proof. exact (@lem4866390 (type686 A) Prop f x). Qed.
Lemma lem4866392 {A : Type'} (f : type639 A) (c : A -> Prop) : (term607 A f c) = (term608 A f c).
Proof. exact (@lem4866391 A (@ARBITRARY A) (@I ((A -> Prop) -> (A -> Prop) -> Prop) f c)). Qed.
Lemma lem4866393 {A : Type'} (f : type639 A) (c : A -> Prop) : (term490 A f c) = (term608 A f c).
Proof. exact (TRANS (@lem4866388 A f c) (@lem4866392 A f c)). Qed.
Lemma lem4866394 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866395 {A : Type'} (f : type639 A) (c : A -> Prop) : (term261 A f c) = (term609 A f c).
Proof. exact (MK_COMB (@lem4866394) (@lem4866393 A f c)). Qed.
Lemma lem4866396 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term610 A P t' f c) = (term611 A P t' f c).
Proof. exact (MK_COMB (@lem4866395 A f c) (@lem4866378 A P t' f c)). Qed.
Lemma lem4866397 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4866402 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4866403 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4866402 (A -> Prop) Prop f x). Qed.
Lemma lem4866405 {A : Type'} (u : type686 A) (c : A -> Prop) : (u c) = (@I ((A -> Prop) -> Prop) u c).
Proof. exact (@lem4866403 A u c). Qed.
Lemma lem4866406 {A : Type'} (u : type686 A) (c : A -> Prop) : (term340 A u c) = (term565 A u c).
Proof. exact (MK_COMB (@lem4866397) (@lem4866405 A u c)). Qed.
Lemma lem4866407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866408 {A : Type'} (u : type686 A) (c : A -> Prop) : (term370 A u c) = (term612 A u c).
Proof. exact (MK_COMB (@lem4866407) (@lem4866406 A u c)). Qed.
Lemma lem4866409 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term535 A u P t' f c) = (term613 A u P t' f c).
Proof. exact (MK_COMB (@lem4866408 A u c) (@lem4866396 A P t' f c)). Qed.
Lemma lem4866410 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term537 A u P t' f) = (term614 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4866409 A u P t' f c)). Qed.
Lemma lem4866411 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866412 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term539 A u P t' f) = (term615 A u P t' f).
Proof. exact (MK_COMB (@lem4866411 A) (@lem4866410 A u P t' f)). Qed.
Lemma lem4866413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866414 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term556 A u P t' f) = (term616 A u P t' f).
Proof. exact (MK_COMB (@lem4866413) (@lem4866412 A u P t' f)). Qed.
Lemma lem4866415 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) : (term558 A P t' f u) = (term617 A P t' f u).
Proof. exact (MK_COMB (@lem4866414 A u P t' f) (@lem4866212 A u)). Qed.
Lemma lem4866416 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term617 A P t' f u.
Proof. exact (EQ_MP (@lem4866415 A P t' f u) (@lem4866059 A P t' f u h1)). Qed.
Lemma lem4866418 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term615 A u P t' f.
Proof. exact (proj1 (@lem4866416 A P t' f u h1)). Qed.
Lemma lem4866419 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1129 A f s t u x.
Proof. exact (h1). Qed.
Lemma lem4866420 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1122 A f u s x.
Proof. exact (h1). Qed.
Lemma lem4866421 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1125 A u x.
Proof. exact (proj2 (@lem4866419 A f s t u x h1)). Qed.
Lemma lem4866422 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1127 A u f s t x.
Proof. exact (proj1 (@lem4866419 A f s t u x h1)). Qed.
Lemma lem4866424 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term564 A u f s t.
Proof. exact (proj1 (@lem4866422 A f s t u x h1)). Qed.
Lemma lem4866427 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1114 A u s x.
Proof. exact (proj2 (@lem4866420 A f u s x h1)). Qed.
Lemma lem4866428 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1120 A u f x.
Proof. exact (proj1 (@lem4866420 A f u s x h1)). Qed.
Lemma lem4866432 {A : Type'} (P : A -> Prop) (Q : Prop) : (term618 A P Q) = (term619 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4866433 {A : Type'} (P : type686 A) (Q : Prop) : (term620 A P Q) = (term621 A P Q).
Proof. exact (@lem4866432 (A -> Prop) P Q). Qed.
Lemma lem4866434 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term623 A f c x).
Proof. exact (@lem4866433 A (term572 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4866435 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4866436 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term625 A f c x) = (term572 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866435 A f c t x)). Qed.
Lemma lem4866437 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866438 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term626 A f c x) = (term573 A f c x).
Proof. exact (MK_COMB (@lem4866437 A) (@lem4866436 A f c x)). Qed.
Lemma lem4866439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866440 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term627 A f c x) = (term574 A f c x).
Proof. exact (MK_COMB (@lem4866439) (@lem4866438 A f c x)). Qed.
Lemma lem4866441 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4866442 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term575 A f c x).
Proof. exact (MK_COMB (@lem4866440 A f c x) (@lem4866441 A c x)). Qed.
Lemma lem4866443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866444 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term628 A f c x) = (term629 A f c x).
Proof. exact (MK_COMB (@lem4866443) (@lem4866442 A f c x)). Qed.
Lemma lem4866445 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4866446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866447 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term630 A f c x t) = (term631 A f c t x).
Proof. exact (MK_COMB (@lem4866446) (@lem4866445 A f c t x)). Qed.
Lemma lem4866448 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4866449 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term632 A f t c x) = (term633 A f t c x).
Proof. exact (MK_COMB (@lem4866447 A f c t x) (@lem4866448 A c x)). Qed.
Lemma lem4866450 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term634 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866449 A f t c x)). Qed.
Lemma lem4866451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866452 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term623 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4866451 A) (@lem4866450 A f c x)). Qed.
Lemma lem4866453 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term622 A f c x) = (term623 A f c x)) = ((term575 A f c x) = (term636 A f c x)).
Proof. exact (MK_COMB (@lem4866444 A f c x) (@lem4866452 A f c x)). Qed.
Lemma lem4866454 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term575 A f c x) = (term636 A f c x).
Proof. exact (EQ_MP (@lem4866453 A f c x) (@lem4866434 A f c x)). Qed.
Lemma lem4866455 {A : Type'} (f : type639 A) (c : A -> Prop) : (term576 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4866454 A f c x)). Qed.
Lemma lem4866456 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866457 {A : Type'} (f : type639 A) (c : A -> Prop) : (term577 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4866456 A) (@lem4866455 A f c)). Qed.
Lemma lem4866458 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term598 A f t' c) = (term598 A f t' c).
Proof. exact (eq_refl (term598 A f t' c)). Qed.
Lemma lem4866459 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4866458 A f t' c) (@lem4866457 A f c)). Qed.
Lemma lem4866461 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4866462 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (@lem4866461 A P Q). Qed.
Lemma lem4866463 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term641 A t' f c).
Proof. exact (@lem4866462 A (term594 A f t' c) (term637 A f c)). Qed.
Lemma lem4866464 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4866465 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term643 A f t' c) = (term594 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4866464 A f t' c x)). Qed.
Lemma lem4866466 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866467 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term644 A f t' c) = (term596 A f t' c).
Proof. exact (MK_COMB (@lem4866466 A) (@lem4866465 A f t' c)). Qed.
Lemma lem4866468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866469 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term645 A f t' c) = (term598 A f t' c).
Proof. exact (MK_COMB (@lem4866468) (@lem4866467 A f t' c)). Qed.
Lemma lem4866470 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4866471 {A : Type'} (f : type639 A) (c : A -> Prop) : (term647 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4866470 A f c x)). Qed.
Lemma lem4866472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866473 {A : Type'} (f : type639 A) (c : A -> Prop) : (term648 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4866472 A) (@lem4866471 A f c)). Qed.
Lemma lem4866474 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4866469 A f t' c) (@lem4866473 A f c)). Qed.
Lemma lem4866475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866476 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term649 A t' f c) = (term650 A t' f c).
Proof. exact (MK_COMB (@lem4866475) (@lem4866474 A t' f c)). Qed.
Lemma lem4866477 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4866478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866479 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term651 A f t' c x) = (term652 A f t' c x).
Proof. exact (MK_COMB (@lem4866478) (@lem4866477 A f t' c x)). Qed.
Lemma lem4866480 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4866481 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term653 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4866479 A f t' c x) (@lem4866480 A f c x)). Qed.
Lemma lem4866482 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term655 A t' f c) = (term656 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866481 A t' f c x)). Qed.
Lemma lem4866483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866484 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term641 A t' f c) = (term657 A t' f c).
Proof. exact (MK_COMB (@lem4866483 A) (@lem4866482 A t' f c)). Qed.
Lemma lem4866485 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term640 A t' f c) = (term641 A t' f c)) = ((term639 A t' f c) = (term657 A t' f c)).
Proof. exact (MK_COMB (@lem4866476 A t' f c) (@lem4866484 A t' f c)). Qed.
Lemma lem4866486 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term657 A t' f c).
Proof. exact (EQ_MP (@lem4866485 A t' f c) (@lem4866463 A t' f c)). Qed.
Lemma lem4866488 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866489 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866488 (A -> Prop) P Q). Qed.
Lemma lem4866490 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term663 A t' f c x).
Proof. exact (@lem4866489 A (term592 A f t' c x) (term635 A f c x)). Qed.
Lemma lem4866491 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4866492 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866491 A f t c x)). Qed.
Lemma lem4866493 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866494 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4866493 A) (@lem4866492 A f c x)). Qed.
Lemma lem4866495 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4866496 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4866495 A f t' c x) (@lem4866494 A f c x)). Qed.
Lemma lem4866497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866498 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term667 A t' f c x) = (term668 A t' f c x).
Proof. exact (MK_COMB (@lem4866497) (@lem4866496 A t' f c x)). Qed.
Lemma lem4866499 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4866500 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4866501 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term669 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (MK_COMB (@lem4866500 A f t' c x) (@lem4866499 A f t c x)). Qed.
Lemma lem4866502 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term671 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866501 A t' f t c x)). Qed.
Lemma lem4866503 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866504 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term663 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4866503 A) (@lem4866502 A t' f c x)). Qed.
Lemma lem4866505 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A t' f c x) = (term663 A t' f c x)) = ((term654 A t' f c x) = (term673 A t' f c x)).
Proof. exact (MK_COMB (@lem4866498 A t' f c x) (@lem4866504 A t' f c x)). Qed.
Lemma lem4866506 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term654 A t' f c x) = (term673 A t' f c x).
Proof. exact (EQ_MP (@lem4866505 A t' f c x) (@lem4866490 A t' f c x)). Qed.
Lemma lem4866507 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term656 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866506 A t' f c x)). Qed.
Lemma lem4866508 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866509 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term657 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4866508 A) (@lem4866507 A t' f c)). Qed.
Lemma lem4866510 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4866486 A t' f c) (@lem4866509 A t' f c)). Qed.
Lemma lem4866511 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4866459 A t' f c) (@lem4866510 A t' f c)). Qed.
Lemma lem4866512 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term604 A f c P) = (term604 A f c P).
Proof. exact (eq_refl (term604 A f c P)). Qed.
Lemma lem4866513 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4866512 A f c P) (@lem4866511 A t' f c)). Qed.
Lemma lem4866517 {A : Type'} (P : A -> Prop) (Q : Prop) : (term677 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4866518 {A : Type'} (P : type686 A) (Q : Prop) : (term679 A P Q) = (term680 A P Q).
Proof. exact (@lem4866517 (A -> Prop) P Q). Qed.
Lemma lem4866519 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term682 A P t' f c).
Proof. exact (@lem4866518 A (term602 A f c P) (term675 A t' f c)). Qed.
Lemma lem4866520 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4866521 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term684 A f c P) = (term602 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866520 A f c P c')). Qed.
Lemma lem4866522 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866523 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term685 A f c P) = (term603 A f c P).
Proof. exact (MK_COMB (@lem4866522 A) (@lem4866521 A f c P)). Qed.
Lemma lem4866524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866525 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term686 A f c P) = (term604 A f c P).
Proof. exact (MK_COMB (@lem4866524) (@lem4866523 A f c P)). Qed.
Lemma lem4866526 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4866527 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4866525 A f c P) (@lem4866526 A t' f c)). Qed.
Lemma lem4866528 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866529 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term687 A P t' f c) = (term688 A P t' f c).
Proof. exact (MK_COMB (@lem4866528) (@lem4866527 A P t' f c)). Qed.
Lemma lem4866530 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4866531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866532 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term689 A f c P c') = (term690 A f c P c').
Proof. exact (MK_COMB (@lem4866531) (@lem4866530 A f c P c')). Qed.
Lemma lem4866533 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4866534 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term691 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866532 A f c P c') (@lem4866533 A t' f c)). Qed.
Lemma lem4866535 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term693 A P t' f c) = (term694 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866534 A P c' t' f c)). Qed.
Lemma lem4866536 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866537 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term682 A P t' f c) = (term695 A P t' f c).
Proof. exact (MK_COMB (@lem4866536 A) (@lem4866535 A P t' f c)). Qed.
Lemma lem4866538 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term681 A P t' f c) = (term682 A P t' f c)) = ((term676 A P t' f c) = (term695 A P t' f c)).
Proof. exact (MK_COMB (@lem4866529 A P t' f c) (@lem4866537 A P t' f c)). Qed.
Lemma lem4866539 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term695 A P t' f c).
Proof. exact (EQ_MP (@lem4866538 A P t' f c) (@lem4866519 A P t' f c)). Qed.
Lemma lem4866541 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866542 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4866541 A P Q). Qed.
Lemma lem4866543 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term697 A P c' t' f c).
Proof. exact (@lem4866542 A (term601 A f c P c') (term674 A t' f c)). Qed.
Lemma lem4866544 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4866545 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term699 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866544 A t' f c x)). Qed.
Lemma lem4866546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866547 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term700 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4866546 A) (@lem4866545 A t' f c)). Qed.
Lemma lem4866548 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866549 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866548 A f c P c') (@lem4866547 A t' f c)). Qed.
Lemma lem4866550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866551 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term701 A P c' t' f c) = (term702 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866550) (@lem4866549 A P c' t' f c)). Qed.
Lemma lem4866552 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4866553 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866554 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866553 A f c P c') (@lem4866552 A t' f c x)). Qed.
Lemma lem4866555 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term705 A P c' t' f c) = (term706 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866554 A P c' t' f c x)). Qed.
Lemma lem4866556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866557 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866556 A) (@lem4866555 A P c' t' f c)). Qed.
Lemma lem4866558 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term696 A P c' t' f c) = (term697 A P c' t' f c)) = ((term692 A P c' t' f c) = (term707 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4866551 A P c' t' f c) (@lem4866557 A P c' t' f c)). Qed.
Lemma lem4866559 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (EQ_MP (@lem4866558 A P c' t' f c) (@lem4866543 A P c' t' f c)). Qed.
Lemma lem4866561 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866562 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866561 (A -> Prop) P Q). Qed.
Lemma lem4866563 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term709 A P c' t' f c x).
Proof. exact (@lem4866562 A (term601 A f c P c') (term672 A t' f c x)). Qed.
Lemma lem4866564 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4866565 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866564 A t' f t c x)). Qed.
Lemma lem4866566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866567 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term712 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4866566 A) (@lem4866565 A t' f c x)). Qed.
Lemma lem4866568 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866569 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866568 A f c P c') (@lem4866567 A t' f c x)). Qed.
Lemma lem4866570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866571 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term713 A P c' t' f c x) = (term714 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866570) (@lem4866569 A P c' t' f c x)). Qed.
Lemma lem4866572 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4866573 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866574 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term715 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866573 A f c P c') (@lem4866572 A t' f t c x)). Qed.
Lemma lem4866575 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term717 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866574 A P c' t' f t c x)). Qed.
Lemma lem4866576 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866577 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term709 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866576 A) (@lem4866575 A P c' t' f c x)). Qed.
Lemma lem4866578 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term708 A P c' t' f c x) = (term709 A P c' t' f c x)) = ((term704 A P c' t' f c x) = (term719 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4866571 A P c' t' f c x) (@lem4866577 A P c' t' f c x)). Qed.
Lemma lem4866579 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term704 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4866578 A P c' t' f c x) (@lem4866563 A P c' t' f c x)). Qed.
Lemma lem4866580 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term706 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866579 A P c' t' f c x)). Qed.
Lemma lem4866581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866582 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term707 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866581 A) (@lem4866580 A P c' t' f c)). Qed.
Lemma lem4866583 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (TRANS (@lem4866559 A P c' t' f c) (@lem4866582 A P c' t' f c)). Qed.
Lemma lem4866584 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term694 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866583 A P c' t' f c)). Qed.
Lemma lem4866585 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866586 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4866585 A) (@lem4866584 A P t' f c)). Qed.
Lemma lem4866587 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4866539 A P t' f c) (@lem4866586 A P t' f c)). Qed.
Lemma lem4866588 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4866513 A P t' f c) (@lem4866587 A P t' f c)). Qed.
Lemma lem4866589 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866590 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4866589 A f c) (@lem4866588 A P t' f c)). Qed.
Lemma lem4866592 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866593 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866592 (A -> Prop) P Q). Qed.
Lemma lem4866594 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term726 A P t' f c).
Proof. exact (@lem4866593 A (term608 A f c) (term722 A P t' f c)). Qed.
Lemma lem4866595 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4866596 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term728 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866595 A P c' t' f c)). Qed.
Lemma lem4866597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866598 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term729 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4866597 A) (@lem4866596 A P t' f c)). Qed.
Lemma lem4866599 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866600 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4866599 A f c) (@lem4866598 A P t' f c)). Qed.
Lemma lem4866601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866602 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term730 A P t' f c) = (term731 A P t' f c).
Proof. exact (MK_COMB (@lem4866601) (@lem4866600 A P t' f c)). Qed.
Lemma lem4866603 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4866604 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866605 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P t' f c c') = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866604 A f c) (@lem4866603 A P c' t' f c)). Qed.
Lemma lem4866606 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term735 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866605 A P c' t' f c)). Qed.
Lemma lem4866607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866608 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term726 A P t' f c) = (term736 A P t' f c).
Proof. exact (MK_COMB (@lem4866607 A) (@lem4866606 A P t' f c)). Qed.
Lemma lem4866609 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term725 A P t' f c) = (term726 A P t' f c)) = ((term724 A P t' f c) = (term736 A P t' f c)).
Proof. exact (MK_COMB (@lem4866602 A P t' f c) (@lem4866608 A P t' f c)). Qed.
Lemma lem4866610 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term736 A P t' f c).
Proof. exact (EQ_MP (@lem4866609 A P t' f c) (@lem4866594 A P t' f c)). Qed.
Lemma lem4866612 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4866612 A P Q). Qed.
Lemma lem4866614 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term738 A P c' t' f c).
Proof. exact (@lem4866613 A (term608 A f c) (term720 A P c' t' f c)). Qed.
Lemma lem4866615 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4866616 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866615 A P c' t' f c x)). Qed.
Lemma lem4866617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866618 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866617 A) (@lem4866616 A P c' t' f c)). Qed.
Lemma lem4866619 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866620 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866619 A f c) (@lem4866618 A P c' t' f c)). Qed.
Lemma lem4866621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866622 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term742 A P c' t' f c) = (term743 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866621) (@lem4866620 A P c' t' f c)). Qed.
Lemma lem4866623 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4866624 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866625 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866624 A f c) (@lem4866623 A P c' t' f c x)). Qed.
Lemma lem4866626 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866625 A P c' t' f c x)). Qed.
Lemma lem4866627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866628 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term738 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866627 A) (@lem4866626 A P c' t' f c)). Qed.
Lemma lem4866629 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term737 A P c' t' f c) = (term738 A P c' t' f c)) = ((term733 A P c' t' f c) = (term748 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4866622 A P c' t' f c) (@lem4866628 A P c' t' f c)). Qed.
Lemma lem4866630 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (EQ_MP (@lem4866629 A P c' t' f c) (@lem4866614 A P c' t' f c)). Qed.
Lemma lem4866632 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866633 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866632 (A -> Prop) P Q). Qed.
Lemma lem4866634 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term750 A P c' t' f c x).
Proof. exact (@lem4866633 A (term608 A f c) (term718 A P c' t' f c x)). Qed.
Lemma lem4866635 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4866636 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866635 A P c' t' f t c x)). Qed.
Lemma lem4866637 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866638 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866637 A) (@lem4866636 A P c' t' f c x)). Qed.
Lemma lem4866639 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866640 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866639 A f c) (@lem4866638 A P c' t' f c x)). Qed.
Lemma lem4866641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866642 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term754 A P c' t' f c x) = (term755 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866641) (@lem4866640 A P c' t' f c x)). Qed.
Lemma lem4866643 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4866644 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866645 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866644 A f c) (@lem4866643 A P c' t' f t c x)). Qed.
Lemma lem4866646 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term758 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866645 A P c' t' f t c x)). Qed.
Lemma lem4866647 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866648 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term750 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866647 A) (@lem4866646 A P c' t' f c x)). Qed.
Lemma lem4866649 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term749 A P c' t' f c x) = (term750 A P c' t' f c x)) = ((term745 A P c' t' f c x) = (term760 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4866642 A P c' t' f c x) (@lem4866648 A P c' t' f c x)). Qed.
Lemma lem4866650 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term745 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4866649 A P c' t' f c x) (@lem4866634 A P c' t' f c x)). Qed.
Lemma lem4866651 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866650 A P c' t' f c x)). Qed.
Lemma lem4866652 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866653 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term748 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866652 A) (@lem4866651 A P c' t' f c)). Qed.
Lemma lem4866654 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (TRANS (@lem4866630 A P c' t' f c) (@lem4866653 A P c' t' f c)). Qed.
Lemma lem4866655 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866654 A P c' t' f c)). Qed.
Lemma lem4866656 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866657 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4866656 A) (@lem4866655 A P t' f c)). Qed.
Lemma lem4866658 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4866610 A P t' f c) (@lem4866657 A P t' f c)). Qed.
Lemma lem4866659 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4866590 A P t' f c) (@lem4866658 A P t' f c)). Qed.
Lemma lem4866660 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866661 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4866660 A u c) (@lem4866659 A P t' f c)). Qed.
Lemma lem4866663 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4866664 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4866663 (A -> Prop) P Q). Qed.
Lemma lem4866665 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term771 A u P t' f c).
Proof. exact (@lem4866664 A (term565 A u c) (term763 A P t' f c)). Qed.
Lemma lem4866666 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4866667 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866666 A P c' t' f c)). Qed.
Lemma lem4866668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866669 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4866668 A) (@lem4866667 A P t' f c)). Qed.
Lemma lem4866670 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866671 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4866670 A u c) (@lem4866669 A P t' f c)). Qed.
Lemma lem4866672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866673 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A u P t' f c) = (term776 A u P t' f c).
Proof. exact (MK_COMB (@lem4866672) (@lem4866671 A u P t' f c)). Qed.
Lemma lem4866674 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4866675 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866676 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A u P t' f c c') = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4866675 A u c) (@lem4866674 A P c' t' f c)). Qed.
Lemma lem4866677 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term779 A u P t' f c) = (term780 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866676 A u P c' t' f c)). Qed.
Lemma lem4866678 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866679 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term771 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (MK_COMB (@lem4866678 A) (@lem4866677 A u P t' f c)). Qed.
Lemma lem4866680 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term770 A u P t' f c) = (term771 A u P t' f c)) = ((term765 A u P t' f c) = (term781 A u P t' f c)).
Proof. exact (MK_COMB (@lem4866673 A u P t' f c) (@lem4866679 A u P t' f c)). Qed.
Lemma lem4866681 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (EQ_MP (@lem4866680 A u P t' f c) (@lem4866665 A u P t' f c)). Qed.
Lemma lem4866683 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4866684 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (@lem4866683 A P Q). Qed.
Lemma lem4866685 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term783 A u P c' t' f c).
Proof. exact (@lem4866684 A (term565 A u c) (term761 A P c' t' f c)). Qed.
Lemma lem4866686 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4866687 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term785 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866686 A P c' t' f c x)). Qed.
Lemma lem4866688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866689 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866688 A) (@lem4866687 A P c' t' f c)). Qed.
Lemma lem4866690 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866691 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4866690 A u c) (@lem4866689 A P c' t' f c)). Qed.
Lemma lem4866692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866693 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A u P c' t' f c) = (term788 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4866692) (@lem4866691 A u P c' t' f c)). Qed.
Lemma lem4866694 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4866695 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866696 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4866695 A u c) (@lem4866694 A P c' t' f c x)). Qed.
Lemma lem4866697 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term791 A u P c' t' f c) = (term792 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866696 A u P c' t' f c x)). Qed.
Lemma lem4866698 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866699 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term783 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4866698 A) (@lem4866697 A u P c' t' f c)). Qed.
Lemma lem4866700 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term782 A u P c' t' f c) = (term783 A u P c' t' f c)) = ((term778 A u P c' t' f c) = (term793 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4866693 A u P c' t' f c) (@lem4866699 A u P c' t' f c)). Qed.
Lemma lem4866701 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4866700 A u P c' t' f c) (@lem4866685 A u P c' t' f c)). Qed.
Lemma lem4866703 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4866704 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4866703 (A -> Prop) P Q). Qed.
Lemma lem4866705 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term795 A u P c' t' f c x).
Proof. exact (@lem4866704 A (term565 A u c) (term759 A P c' t' f c x)). Qed.
Lemma lem4866706 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4866707 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term797 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866706 A P c' t' f t c x)). Qed.
Lemma lem4866708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866709 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866708 A) (@lem4866707 A P c' t' f c x)). Qed.
Lemma lem4866710 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866711 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4866710 A u c) (@lem4866709 A P c' t' f c x)). Qed.
Lemma lem4866712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866713 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term799 A u P c' t' f c x) = (term800 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4866712) (@lem4866711 A u P c' t' f c x)). Qed.
Lemma lem4866714 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4866715 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866716 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term801 A u P c' t' f c x t) = (term802 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866715 A u c) (@lem4866714 A P c' t' f t c x)). Qed.
Lemma lem4866717 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term803 A u P c' t' f c x) = (term804 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866716 A u P c' t' f t c x)). Qed.
Lemma lem4866718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866719 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term795 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4866718 A) (@lem4866717 A u P c' t' f c x)). Qed.
Lemma lem4866720 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term794 A u P c' t' f c x) = (term795 A u P c' t' f c x)) = ((term790 A u P c' t' f c x) = (term805 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4866713 A u P c' t' f c x) (@lem4866719 A u P c' t' f c x)). Qed.
Lemma lem4866721 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4866720 A u P c' t' f c x) (@lem4866705 A u P c' t' f c x)). Qed.
Lemma lem4866722 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term792 A u P c' t' f c) = (term806 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866721 A u P c' t' f c x)). Qed.
Lemma lem4866723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866724 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term793 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4866723 A) (@lem4866722 A u P c' t' f c)). Qed.
Lemma lem4866725 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (TRANS (@lem4866701 A u P c' t' f c) (@lem4866724 A u P c' t' f c)). Qed.
Lemma lem4866726 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A u P t' f c) = (term808 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866725 A u P c' t' f c)). Qed.
Lemma lem4866727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866728 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (MK_COMB (@lem4866727 A) (@lem4866726 A u P t' f c)). Qed.
Lemma lem4866729 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4866681 A u P t' f c) (@lem4866728 A u P t' f c)). Qed.
Lemma lem4866730 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4866661 A u P t' f c) (@lem4866729 A u P t' f c)). Qed.
Lemma lem4866731 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term614 A u P t' f) = (term810 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4866730 A u P t' f c)). Qed.
Lemma lem4866732 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866733 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term615 A u P t' f) = (term811 A u P t' f).
Proof. exact (MK_COMB (@lem4866732 A) (@lem4866731 A u P t' f)). Qed.
Lemma lem4866746 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term633 A f t c x) = (term633 A f t c x).
Proof. exact (eq_refl (term633 A f t c x)). Qed.
Lemma lem4866763 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term592 A f t' c x) = (term812 A f t' c x).
Proof. exact (@lem19699 (term584 A f t' c x) (term580 A t' c x) (term566 A c x)). Qed.
Lemma lem4866764 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866765 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term813 A f t' c x).
Proof. exact (MK_COMB (@lem4866764) (@lem4866763 A f t' c x)). Qed.
Lemma lem4866766 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term670 A t' f t c x) = (term814 A t' f t c x).
Proof. exact (MK_COMB (@lem4866765 A f t' c x) (@lem4866746 A f t c x)). Qed.
Lemma lem4866775 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866776 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term716 A P c' t' f t c x) = (term815 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866775 A f c P c') (@lem4866766 A t' f t c x)). Qed.
Lemma lem4866779 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4866780 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term757 A P c' t' f t c x) = (term816 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866779 A f c) (@lem4866776 A P c' t' f t c x)). Qed.
Lemma lem4866783 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4866784 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term817 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866783 A u c) (@lem4866780 A P c' t' f t c x)). Qed.
Lemma lem4866785 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term818 A u P c' t' f t c x).
Proof. exact (@lem19490 (term608 A f c) (term565 A u c) (term815 A P c' t' f t c x)). Qed.
Lemma lem4866786 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term820 A P c' u t' f t c x).
Proof. exact (@lem19490 (term601 A f c P c') (term565 A u c) (term814 A t' f t c x)). Qed.
Lemma lem4866787 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term822 A t' u f t c x).
Proof. exact (@lem19490 (term812 A f t' c x) (term565 A u c) (term633 A f t c x)). Qed.
Lemma lem4866788 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term823 A u f t c x) = (term823 A u f t c x).
Proof. exact (eq_refl (term823 A u f t c x)). Qed.
Lemma lem4866795 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term824 A u f t' c x) = (term825 A f u t' c x).
Proof. exact (@lem19490 (term826 A f t' c x) (term565 A u c) (term827 A t' c x)). Qed.
Lemma lem4866796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866797 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term828 A u f t' c x) = (term829 A f u t' c x).
Proof. exact (MK_COMB (@lem4866796) (@lem4866795 A f u t' c x)). Qed.
Lemma lem4866798 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term822 A t' u f t c x) = (term830 A t' u f t c x).
Proof. exact (MK_COMB (@lem4866797 A f u t' c x) (@lem4866788 A u f t c x)). Qed.
Lemma lem4866799 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term830 A t' u f t c x).
Proof. exact (TRANS (@lem4866787 A t' u f t c x) (@lem4866798 A t' u f t c x)). Qed.
Lemma lem4866802 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term831 A u f c P c') = (term831 A u f c P c').
Proof. exact (eq_refl (term831 A u f c P c')). Qed.
Lemma lem4866803 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term820 A P c' u t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4866802 A u f c P c') (@lem4866799 A t' u f t c x)). Qed.
Lemma lem4866804 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4866786 A P c' u t' f t c x) (@lem4866803 A P c' t' u f t c x)). Qed.
Lemma lem4866807 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term833 A u f c) = (term833 A u f c).
Proof. exact (eq_refl (term833 A u f c)). Qed.
Lemma lem4866808 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term818 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4866807 A u f c) (@lem4866804 A P c' t' u f t c x)). Qed.
Lemma lem4866809 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4866785 A u P c' t' f t c x) (@lem4866808 A P c' t' u f t c x)). Qed.
Lemma lem4866810 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4866784 A u P c' t' f t c x) (@lem4866809 A P c' t' u f t c x)). Qed.
Lemma lem4866811 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term804 A u P c' t' f c x) = (term835 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866810 A P c' t' u f t c x)). Qed.
Lemma lem4866812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866813 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term805 A u P c' t' f c x) = (term836 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4866812 A) (@lem4866811 A P c' t' u f c x)). Qed.
Lemma lem4866814 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term806 A u P c' t' f c) = (term837 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4866813 A P c' t' u f c x)). Qed.
Lemma lem4866815 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866816 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term807 A u P c' t' f c) = (term838 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4866815 A) (@lem4866814 A P c' t' u f c)). Qed.
Lemma lem4866817 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term808 A u P t' f c) = (term839 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866816 A P c' t' u f c)). Qed.
Lemma lem4866818 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866819 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term809 A u P t' f c) = (term840 A P t' u f c).
Proof. exact (MK_COMB (@lem4866818 A) (@lem4866817 A P t' u f c)). Qed.
Lemma lem4866820 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term810 A u P t' f) = (term841 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4866819 A P t' u f c)). Qed.
Lemma lem4866821 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866822 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term811 A u P t' f) = (term842 A P t' u f).
Proof. exact (MK_COMB (@lem4866821 A) (@lem4866820 A P t' u f)). Qed.
Lemma lem4866823 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term615 A u P t' f) = (term842 A P t' u f).
Proof. exact (TRANS (@lem4866733 A u P t' f) (@lem4866822 A P t' u f)). Qed.
Lemma lem4866824 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term842 A P t' u f.
Proof. exact (EQ_MP (@lem4866823 A P t' u f) (@lem4866418 A P t' f u h1)). Qed.
Lemma lem4866836 {A : Type'} (u : type686 A) (t : A -> Prop) (x : A) : (term1123 A u t x) = (term1123 A u t x).
Proof. exact (eq_refl (term1123 A u t x)). Qed.
Lemma lem4866837 {A : Type'} (u : type686 A) (x : A) : (term1124 A u x) = (term1124 A u x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866836 A u t x)). Qed.
Lemma lem4866838 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866840 {A : Type'} (u : type686 A) (x : A) : (term1125 A u x) = (term1125 A u x).
Proof. exact (MK_COMB (@lem4866838 A) (@lem4866837 A u x)). Qed.
Lemma lem4866841 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1125 A u x.
Proof. exact (EQ_MP (@lem4866840 A u x) (@lem4866421 A f s t u x h1)). Qed.
Lemma lem4866855 {A : Type'} (P : A -> Prop) (Q : Prop) : (term618 A P Q) = (term619 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4866856 {A : Type'} (P : type686 A) (Q : Prop) : (term620 A P Q) = (term621 A P Q).
Proof. exact (@lem4866855 (A -> Prop) P Q). Qed.
Lemma lem4866857 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term623 A f c x).
Proof. exact (@lem4866856 A (term572 A f c x) (@I (A -> Prop) c x)). Qed.
Lemma lem4866858 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4866859 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term625 A f c x) = (term572 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866858 A f c t x)). Qed.
Lemma lem4866860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866861 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term626 A f c x) = (term573 A f c x).
Proof. exact (MK_COMB (@lem4866860 A) (@lem4866859 A f c x)). Qed.
Lemma lem4866862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866863 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term627 A f c x) = (term574 A f c x).
Proof. exact (MK_COMB (@lem4866862) (@lem4866861 A f c x)). Qed.
Lemma lem4866864 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4866865 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term622 A f c x) = (term575 A f c x).
Proof. exact (MK_COMB (@lem4866863 A f c x) (@lem4866864 A c x)). Qed.
Lemma lem4866866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866867 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term628 A f c x) = (term629 A f c x).
Proof. exact (MK_COMB (@lem4866866) (@lem4866865 A f c x)). Qed.
Lemma lem4866868 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term624 A f c x t) = (term571 A f c t x).
Proof. exact (eq_refl (term624 A f c x t)). Qed.
Lemma lem4866869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4866870 {A : Type'} (f : type639 A) (c : A -> Prop) (t : A -> Prop) (x : A) : (term630 A f c x t) = (term631 A f c t x).
Proof. exact (MK_COMB (@lem4866869) (@lem4866868 A f c t x)). Qed.
Lemma lem4866871 {A : Type'} (c : A -> Prop) (x : A) : (@I (A -> Prop) c x) = (@I (A -> Prop) c x).
Proof. exact (eq_refl (@I (A -> Prop) c x)). Qed.
Lemma lem4866872 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term632 A f t c x) = (term633 A f t c x).
Proof. exact (MK_COMB (@lem4866870 A f c t x) (@lem4866871 A c x)). Qed.
Lemma lem4866873 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term634 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866872 A f t c x)). Qed.
Lemma lem4866874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866875 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term623 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4866874 A) (@lem4866873 A f c x)). Qed.
Lemma lem4866876 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : ((term622 A f c x) = (term623 A f c x)) = ((term575 A f c x) = (term636 A f c x)).
Proof. exact (MK_COMB (@lem4866867 A f c x) (@lem4866875 A f c x)). Qed.
Lemma lem4866877 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term575 A f c x) = (term636 A f c x).
Proof. exact (EQ_MP (@lem4866876 A f c x) (@lem4866857 A f c x)). Qed.
Lemma lem4866878 {A : Type'} (f : type639 A) (c : A -> Prop) : (term576 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4866877 A f c x)). Qed.
Lemma lem4866879 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866880 {A : Type'} (f : type639 A) (c : A -> Prop) : (term577 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4866879 A) (@lem4866878 A f c)). Qed.
Lemma lem4866881 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term598 A f t' c) = (term598 A f t' c).
Proof. exact (eq_refl (term598 A f t' c)). Qed.
Lemma lem4866882 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4866881 A f t' c) (@lem4866880 A f c)). Qed.
Lemma lem4866884 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4866885 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term378 A P Q) = (term377 A P Q).
Proof. exact (@lem4866884 A P Q). Qed.
Lemma lem4866886 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term641 A t' f c).
Proof. exact (@lem4866885 A (term594 A f t' c) (term637 A f c)). Qed.
Lemma lem4866887 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4866888 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term643 A f t' c) = (term594 A f t' c).
Proof. exact (fun_ext (fun x : A => @lem4866887 A f t' c x)). Qed.
Lemma lem4866889 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866890 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term644 A f t' c) = (term596 A f t' c).
Proof. exact (MK_COMB (@lem4866889 A) (@lem4866888 A f t' c)). Qed.
Lemma lem4866891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866892 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) : (term645 A f t' c) = (term598 A f t' c).
Proof. exact (MK_COMB (@lem4866891) (@lem4866890 A f t' c)). Qed.
Lemma lem4866893 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4866894 {A : Type'} (f : type639 A) (c : A -> Prop) : (term647 A f c) = (term637 A f c).
Proof. exact (fun_ext (fun x : A => @lem4866893 A f c x)). Qed.
Lemma lem4866895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866896 {A : Type'} (f : type639 A) (c : A -> Prop) : (term648 A f c) = (term638 A f c).
Proof. exact (MK_COMB (@lem4866895 A) (@lem4866894 A f c)). Qed.
Lemma lem4866897 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term640 A t' f c) = (term639 A t' f c).
Proof. exact (MK_COMB (@lem4866892 A f t' c) (@lem4866896 A f c)). Qed.
Lemma lem4866898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866899 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term649 A t' f c) = (term650 A t' f c).
Proof. exact (MK_COMB (@lem4866898) (@lem4866897 A t' f c)). Qed.
Lemma lem4866900 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term642 A f t' c x) = (term592 A f t' c x).
Proof. exact (eq_refl (term642 A f t' c x)). Qed.
Lemma lem4866901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866902 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term651 A f t' c x) = (term652 A f t' c x).
Proof. exact (MK_COMB (@lem4866901) (@lem4866900 A f t' c x)). Qed.
Lemma lem4866903 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term646 A f c x) = (term636 A f c x).
Proof. exact (eq_refl (term646 A f c x)). Qed.
Lemma lem4866904 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term653 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4866902 A f t' c x) (@lem4866903 A f c x)). Qed.
Lemma lem4866905 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term655 A t' f c) = (term656 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866904 A t' f c x)). Qed.
Lemma lem4866906 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866907 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term641 A t' f c) = (term657 A t' f c).
Proof. exact (MK_COMB (@lem4866906 A) (@lem4866905 A t' f c)). Qed.
Lemma lem4866908 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term640 A t' f c) = (term641 A t' f c)) = ((term639 A t' f c) = (term657 A t' f c)).
Proof. exact (MK_COMB (@lem4866899 A t' f c) (@lem4866907 A t' f c)). Qed.
Lemma lem4866909 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term657 A t' f c).
Proof. exact (EQ_MP (@lem4866908 A t' f c) (@lem4866886 A t' f c)). Qed.
Lemma lem4866911 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866912 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866911 (A -> Prop) P Q). Qed.
Lemma lem4866913 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term663 A t' f c x).
Proof. exact (@lem4866912 A (term592 A f t' c x) (term635 A f c x)). Qed.
Lemma lem4866914 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4866915 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term665 A f c x) = (term635 A f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866914 A f t c x)). Qed.
Lemma lem4866916 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866917 {A : Type'} (f : type639 A) (c : A -> Prop) (x : A) : (term666 A f c x) = (term636 A f c x).
Proof. exact (MK_COMB (@lem4866916 A) (@lem4866915 A f c x)). Qed.
Lemma lem4866918 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4866919 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term662 A t' f c x) = (term654 A t' f c x).
Proof. exact (MK_COMB (@lem4866918 A f t' c x) (@lem4866917 A f c x)). Qed.
Lemma lem4866920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866921 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term667 A t' f c x) = (term668 A t' f c x).
Proof. exact (MK_COMB (@lem4866920) (@lem4866919 A t' f c x)). Qed.
Lemma lem4866922 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term664 A f c x t) = (term633 A f t c x).
Proof. exact (eq_refl (term664 A f c x t)). Qed.
Lemma lem4866923 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term652 A f t' c x).
Proof. exact (eq_refl (term652 A f t' c x)). Qed.
Lemma lem4866924 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term669 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (MK_COMB (@lem4866923 A f t' c x) (@lem4866922 A f t c x)). Qed.
Lemma lem4866925 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term671 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866924 A t' f t c x)). Qed.
Lemma lem4866926 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866927 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term663 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4866926 A) (@lem4866925 A t' f c x)). Qed.
Lemma lem4866928 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term662 A t' f c x) = (term663 A t' f c x)) = ((term654 A t' f c x) = (term673 A t' f c x)).
Proof. exact (MK_COMB (@lem4866921 A t' f c x) (@lem4866927 A t' f c x)). Qed.
Lemma lem4866929 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term654 A t' f c x) = (term673 A t' f c x).
Proof. exact (EQ_MP (@lem4866928 A t' f c x) (@lem4866913 A t' f c x)). Qed.
Lemma lem4866930 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term656 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866929 A t' f c x)). Qed.
Lemma lem4866931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866932 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term657 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4866931 A) (@lem4866930 A t' f c)). Qed.
Lemma lem4866933 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term639 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4866909 A t' f c) (@lem4866932 A t' f c)). Qed.
Lemma lem4866934 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term600 A t' f c) = (term675 A t' f c).
Proof. exact (TRANS (@lem4866882 A t' f c) (@lem4866933 A t' f c)). Qed.
Lemma lem4866935 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term604 A f c P) = (term604 A f c P).
Proof. exact (eq_refl (term604 A f c P)). Qed.
Lemma lem4866936 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4866935 A f c P) (@lem4866934 A t' f c)). Qed.
Lemma lem4866940 {A : Type'} (P : A -> Prop) (Q : Prop) : (term677 A P Q) = (term678 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem4866941 {A : Type'} (P : type686 A) (Q : Prop) : (term679 A P Q) = (term680 A P Q).
Proof. exact (@lem4866940 (A -> Prop) P Q). Qed.
Lemma lem4866942 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term682 A P t' f c).
Proof. exact (@lem4866941 A (term602 A f c P) (term675 A t' f c)). Qed.
Lemma lem4866943 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4866944 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term684 A f c P) = (term602 A f c P).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866943 A f c P c')). Qed.
Lemma lem4866945 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866946 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term685 A f c P) = (term603 A f c P).
Proof. exact (MK_COMB (@lem4866945 A) (@lem4866944 A f c P)). Qed.
Lemma lem4866947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866948 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) : (term686 A f c P) = (term604 A f c P).
Proof. exact (MK_COMB (@lem4866947) (@lem4866946 A f c P)). Qed.
Lemma lem4866949 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4866950 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term681 A P t' f c) = (term676 A P t' f c).
Proof. exact (MK_COMB (@lem4866948 A f c P) (@lem4866949 A t' f c)). Qed.
Lemma lem4866951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866952 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term687 A P t' f c) = (term688 A P t' f c).
Proof. exact (MK_COMB (@lem4866951) (@lem4866950 A P t' f c)). Qed.
Lemma lem4866953 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term683 A f c P c') = (term601 A f c P c').
Proof. exact (eq_refl (term683 A f c P c')). Qed.
Lemma lem4866954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4866955 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term689 A f c P c') = (term690 A f c P c').
Proof. exact (MK_COMB (@lem4866954) (@lem4866953 A f c P c')). Qed.
Lemma lem4866956 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term675 A t' f c) = (term675 A t' f c).
Proof. exact (eq_refl (term675 A t' f c)). Qed.
Lemma lem4866957 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term691 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866955 A f c P c') (@lem4866956 A t' f c)). Qed.
Lemma lem4866958 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term693 A P t' f c) = (term694 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4866957 A P c' t' f c)). Qed.
Lemma lem4866959 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866960 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term682 A P t' f c) = (term695 A P t' f c).
Proof. exact (MK_COMB (@lem4866959 A) (@lem4866958 A P t' f c)). Qed.
Lemma lem4866961 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term681 A P t' f c) = (term682 A P t' f c)) = ((term676 A P t' f c) = (term695 A P t' f c)).
Proof. exact (MK_COMB (@lem4866952 A P t' f c) (@lem4866960 A P t' f c)). Qed.
Lemma lem4866962 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term695 A P t' f c).
Proof. exact (EQ_MP (@lem4866961 A P t' f c) (@lem4866942 A P t' f c)). Qed.
Lemma lem4866964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866965 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4866964 A P Q). Qed.
Lemma lem4866966 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term697 A P c' t' f c).
Proof. exact (@lem4866965 A (term601 A f c P c') (term674 A t' f c)). Qed.
Lemma lem4866967 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4866968 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term699 A t' f c) = (term674 A t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866967 A t' f c x)). Qed.
Lemma lem4866969 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866970 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term700 A t' f c) = (term675 A t' f c).
Proof. exact (MK_COMB (@lem4866969 A) (@lem4866968 A t' f c)). Qed.
Lemma lem4866971 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866972 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term696 A P c' t' f c) = (term692 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866971 A f c P c') (@lem4866970 A t' f c)). Qed.
Lemma lem4866973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866974 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term701 A P c' t' f c) = (term702 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866973) (@lem4866972 A P c' t' f c)). Qed.
Lemma lem4866975 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term698 A t' f c x) = (term673 A t' f c x).
Proof. exact (eq_refl (term698 A t' f c x)). Qed.
Lemma lem4866976 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866977 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term703 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866976 A f c P c') (@lem4866975 A t' f c x)). Qed.
Lemma lem4866978 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term705 A P c' t' f c) = (term706 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4866977 A P c' t' f c x)). Qed.
Lemma lem4866979 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4866980 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term697 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (MK_COMB (@lem4866979 A) (@lem4866978 A P c' t' f c)). Qed.
Lemma lem4866981 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term696 A P c' t' f c) = (term697 A P c' t' f c)) = ((term692 A P c' t' f c) = (term707 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4866974 A P c' t' f c) (@lem4866980 A P c' t' f c)). Qed.
Lemma lem4866982 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term707 A P c' t' f c).
Proof. exact (EQ_MP (@lem4866981 A P c' t' f c) (@lem4866966 A P c' t' f c)). Qed.
Lemma lem4866984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4866985 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4866984 (A -> Prop) P Q). Qed.
Lemma lem4866986 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term709 A P c' t' f c x).
Proof. exact (@lem4866985 A (term601 A f c P c') (term672 A t' f c x)). Qed.
Lemma lem4866987 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4866988 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term711 A t' f c x) = (term672 A t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866987 A t' f t c x)). Qed.
Lemma lem4866989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4866990 {A : Type'} (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term712 A t' f c x) = (term673 A t' f c x).
Proof. exact (MK_COMB (@lem4866989 A) (@lem4866988 A t' f c x)). Qed.
Lemma lem4866991 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866992 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term708 A P c' t' f c x) = (term704 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866991 A f c P c') (@lem4866990 A t' f c x)). Qed.
Lemma lem4866993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4866994 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term713 A P c' t' f c x) = (term714 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866993) (@lem4866992 A P c' t' f c x)). Qed.
Lemma lem4866995 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term710 A t' f c x t) = (term670 A t' f t c x).
Proof. exact (eq_refl (term710 A t' f c x t)). Qed.
Lemma lem4866996 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4866997 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term715 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4866996 A f c P c') (@lem4866995 A t' f t c x)). Qed.
Lemma lem4866998 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term717 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4866997 A P c' t' f t c x)). Qed.
Lemma lem4866999 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867000 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term709 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4866999 A) (@lem4866998 A P c' t' f c x)). Qed.
Lemma lem4867001 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term708 A P c' t' f c x) = (term709 A P c' t' f c x)) = ((term704 A P c' t' f c x) = (term719 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4866994 A P c' t' f c x) (@lem4867000 A P c' t' f c x)). Qed.
Lemma lem4867002 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term704 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4867001 A P c' t' f c x) (@lem4866986 A P c' t' f c x)). Qed.
Lemma lem4867003 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term706 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867002 A P c' t' f c x)). Qed.
Lemma lem4867004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867005 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term707 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867004 A) (@lem4867003 A P c' t' f c)). Qed.
Lemma lem4867006 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term692 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (TRANS (@lem4866982 A P c' t' f c) (@lem4867005 A P c' t' f c)). Qed.
Lemma lem4867007 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term694 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867006 A P c' t' f c)). Qed.
Lemma lem4867008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867009 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term695 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4867008 A) (@lem4867007 A P t' f c)). Qed.
Lemma lem4867010 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term676 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4866962 A P t' f c) (@lem4867009 A P t' f c)). Qed.
Lemma lem4867011 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term606 A P t' f c) = (term723 A P t' f c).
Proof. exact (TRANS (@lem4866936 A P t' f c) (@lem4867010 A P t' f c)). Qed.
Lemma lem4867012 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867013 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4867012 A f c) (@lem4867011 A P t' f c)). Qed.
Lemma lem4867015 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4867016 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4867015 (A -> Prop) P Q). Qed.
Lemma lem4867017 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term726 A P t' f c).
Proof. exact (@lem4867016 A (term608 A f c) (term722 A P t' f c)). Qed.
Lemma lem4867018 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4867019 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term728 A P t' f c) = (term722 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867018 A P c' t' f c)). Qed.
Lemma lem4867020 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867021 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term729 A P t' f c) = (term723 A P t' f c).
Proof. exact (MK_COMB (@lem4867020 A) (@lem4867019 A P t' f c)). Qed.
Lemma lem4867022 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867023 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term725 A P t' f c) = (term724 A P t' f c).
Proof. exact (MK_COMB (@lem4867022 A f c) (@lem4867021 A P t' f c)). Qed.
Lemma lem4867024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867025 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term730 A P t' f c) = (term731 A P t' f c).
Proof. exact (MK_COMB (@lem4867024) (@lem4867023 A P t' f c)). Qed.
Lemma lem4867026 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term727 A P t' f c c') = (term721 A P c' t' f c).
Proof. exact (eq_refl (term727 A P t' f c c')). Qed.
Lemma lem4867027 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867028 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term732 A P t' f c c') = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867027 A f c) (@lem4867026 A P c' t' f c)). Qed.
Lemma lem4867029 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term734 A P t' f c) = (term735 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867028 A P c' t' f c)). Qed.
Lemma lem4867030 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867031 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term726 A P t' f c) = (term736 A P t' f c).
Proof. exact (MK_COMB (@lem4867030 A) (@lem4867029 A P t' f c)). Qed.
Lemma lem4867032 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term725 A P t' f c) = (term726 A P t' f c)) = ((term724 A P t' f c) = (term736 A P t' f c)).
Proof. exact (MK_COMB (@lem4867025 A P t' f c) (@lem4867031 A P t' f c)). Qed.
Lemma lem4867033 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term736 A P t' f c).
Proof. exact (EQ_MP (@lem4867032 A P t' f c) (@lem4867017 A P t' f c)). Qed.
Lemma lem4867035 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4867036 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (@lem4867035 A P Q). Qed.
Lemma lem4867037 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term738 A P c' t' f c).
Proof. exact (@lem4867036 A (term608 A f c) (term720 A P c' t' f c)). Qed.
Lemma lem4867038 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4867039 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term740 A P c' t' f c) = (term720 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867038 A P c' t' f c x)). Qed.
Lemma lem4867040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867041 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term741 A P c' t' f c) = (term721 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867040 A) (@lem4867039 A P c' t' f c)). Qed.
Lemma lem4867042 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867043 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term737 A P c' t' f c) = (term733 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867042 A f c) (@lem4867041 A P c' t' f c)). Qed.
Lemma lem4867044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867045 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term742 A P c' t' f c) = (term743 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867044) (@lem4867043 A P c' t' f c)). Qed.
Lemma lem4867046 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term739 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (eq_refl (term739 A P c' t' f c x)). Qed.
Lemma lem4867047 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867048 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term744 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867047 A f c) (@lem4867046 A P c' t' f c x)). Qed.
Lemma lem4867049 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term746 A P c' t' f c) = (term747 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867048 A P c' t' f c x)). Qed.
Lemma lem4867050 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867051 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term738 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867050 A) (@lem4867049 A P c' t' f c)). Qed.
Lemma lem4867052 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term737 A P c' t' f c) = (term738 A P c' t' f c)) = ((term733 A P c' t' f c) = (term748 A P c' t' f c)).
Proof. exact (MK_COMB (@lem4867045 A P c' t' f c) (@lem4867051 A P c' t' f c)). Qed.
Lemma lem4867053 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term748 A P c' t' f c).
Proof. exact (EQ_MP (@lem4867052 A P c' t' f c) (@lem4867037 A P c' t' f c)). Qed.
Lemma lem4867055 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4867056 {A : Type'} (P : Prop) (Q : type686 A) : (term660 A P Q) = (term661 A P Q).
Proof. exact (@lem4867055 (A -> Prop) P Q). Qed.
Lemma lem4867057 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term750 A P c' t' f c x).
Proof. exact (@lem4867056 A (term608 A f c) (term718 A P c' t' f c x)). Qed.
Lemma lem4867058 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4867059 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term752 A P c' t' f c x) = (term718 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867058 A P c' t' f t c x)). Qed.
Lemma lem4867060 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867061 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term753 A P c' t' f c x) = (term719 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867060 A) (@lem4867059 A P c' t' f c x)). Qed.
Lemma lem4867062 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867063 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term749 A P c' t' f c x) = (term745 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867062 A f c) (@lem4867061 A P c' t' f c x)). Qed.
Lemma lem4867064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867065 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term754 A P c' t' f c x) = (term755 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867064) (@lem4867063 A P c' t' f c x)). Qed.
Lemma lem4867066 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term751 A P c' t' f c x t) = (term716 A P c' t' f t c x).
Proof. exact (eq_refl (term751 A P c' t' f c x t)). Qed.
Lemma lem4867067 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867068 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term756 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4867067 A f c) (@lem4867066 A P c' t' f t c x)). Qed.
Lemma lem4867069 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term758 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867068 A P c' t' f t c x)). Qed.
Lemma lem4867070 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867071 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term750 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867070 A) (@lem4867069 A P c' t' f c x)). Qed.
Lemma lem4867072 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term749 A P c' t' f c x) = (term750 A P c' t' f c x)) = ((term745 A P c' t' f c x) = (term760 A P c' t' f c x)).
Proof. exact (MK_COMB (@lem4867065 A P c' t' f c x) (@lem4867071 A P c' t' f c x)). Qed.
Lemma lem4867073 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term745 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (EQ_MP (@lem4867072 A P c' t' f c x) (@lem4867057 A P c' t' f c x)). Qed.
Lemma lem4867074 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term747 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867073 A P c' t' f c x)). Qed.
Lemma lem4867075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867076 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term748 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867075 A) (@lem4867074 A P c' t' f c)). Qed.
Lemma lem4867077 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term733 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (TRANS (@lem4867053 A P c' t' f c) (@lem4867076 A P c' t' f c)). Qed.
Lemma lem4867078 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term735 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867077 A P c' t' f c)). Qed.
Lemma lem4867079 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867080 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term736 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4867079 A) (@lem4867078 A P t' f c)). Qed.
Lemma lem4867081 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term724 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4867033 A P t' f c) (@lem4867080 A P t' f c)). Qed.
Lemma lem4867082 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term611 A P t' f c) = (term764 A P t' f c).
Proof. exact (TRANS (@lem4867013 A P t' f c) (@lem4867081 A P t' f c)). Qed.
Lemma lem4867083 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867084 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4867083 A u c) (@lem4867082 A P t' f c)). Qed.
Lemma lem4867086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4867087 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4867086 (A -> Prop) P Q). Qed.
Lemma lem4867088 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term771 A u P t' f c).
Proof. exact (@lem4867087 A (term565 A u c) (term763 A P t' f c)). Qed.
Lemma lem4867089 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4867090 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term773 A P t' f c) = (term763 A P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867089 A P c' t' f c)). Qed.
Lemma lem4867091 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867092 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term774 A P t' f c) = (term764 A P t' f c).
Proof. exact (MK_COMB (@lem4867091 A) (@lem4867090 A P t' f c)). Qed.
Lemma lem4867093 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867094 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term770 A u P t' f c) = (term765 A u P t' f c).
Proof. exact (MK_COMB (@lem4867093 A u c) (@lem4867092 A P t' f c)). Qed.
Lemma lem4867095 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867096 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term775 A u P t' f c) = (term776 A u P t' f c).
Proof. exact (MK_COMB (@lem4867095) (@lem4867094 A u P t' f c)). Qed.
Lemma lem4867097 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term772 A P t' f c c') = (term762 A P c' t' f c).
Proof. exact (eq_refl (term772 A P t' f c c')). Qed.
Lemma lem4867098 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867099 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term777 A u P t' f c c') = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4867098 A u c) (@lem4867097 A P c' t' f c)). Qed.
Lemma lem4867100 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term779 A u P t' f c) = (term780 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867099 A u P c' t' f c)). Qed.
Lemma lem4867101 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867102 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term771 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (MK_COMB (@lem4867101 A) (@lem4867100 A u P t' f c)). Qed.
Lemma lem4867103 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term770 A u P t' f c) = (term771 A u P t' f c)) = ((term765 A u P t' f c) = (term781 A u P t' f c)).
Proof. exact (MK_COMB (@lem4867096 A u P t' f c) (@lem4867102 A u P t' f c)). Qed.
Lemma lem4867104 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term781 A u P t' f c).
Proof. exact (EQ_MP (@lem4867103 A u P t' f c) (@lem4867088 A u P t' f c)). Qed.
Lemma lem4867106 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4867107 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (@lem4867106 A P Q). Qed.
Lemma lem4867108 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term783 A u P c' t' f c).
Proof. exact (@lem4867107 A (term565 A u c) (term761 A P c' t' f c)). Qed.
Lemma lem4867109 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4867110 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term785 A P c' t' f c) = (term761 A P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867109 A P c' t' f c x)). Qed.
Lemma lem4867111 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867112 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term786 A P c' t' f c) = (term762 A P c' t' f c).
Proof. exact (MK_COMB (@lem4867111 A) (@lem4867110 A P c' t' f c)). Qed.
Lemma lem4867113 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867114 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term782 A u P c' t' f c) = (term778 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4867113 A u c) (@lem4867112 A P c' t' f c)). Qed.
Lemma lem4867115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867116 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term787 A u P c' t' f c) = (term788 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4867115) (@lem4867114 A u P c' t' f c)). Qed.
Lemma lem4867117 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term784 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (eq_refl (term784 A P c' t' f c x)). Qed.
Lemma lem4867118 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867119 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term789 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4867118 A u c) (@lem4867117 A P c' t' f c x)). Qed.
Lemma lem4867120 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term791 A u P c' t' f c) = (term792 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867119 A u P c' t' f c x)). Qed.
Lemma lem4867121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867122 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term783 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4867121 A) (@lem4867120 A u P c' t' f c)). Qed.
Lemma lem4867123 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : ((term782 A u P c' t' f c) = (term783 A u P c' t' f c)) = ((term778 A u P c' t' f c) = (term793 A u P c' t' f c)).
Proof. exact (MK_COMB (@lem4867116 A u P c' t' f c) (@lem4867122 A u P c' t' f c)). Qed.
Lemma lem4867124 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term793 A u P c' t' f c).
Proof. exact (EQ_MP (@lem4867123 A u P c' t' f c) (@lem4867108 A u P c' t' f c)). Qed.
Lemma lem4867126 {A : Type'} (P : Prop) (Q : A -> Prop) : (term766 A P Q) = (term767 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4867127 {A : Type'} (P : Prop) (Q : type686 A) : (term768 A P Q) = (term769 A P Q).
Proof. exact (@lem4867126 (A -> Prop) P Q). Qed.
Lemma lem4867128 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term795 A u P c' t' f c x).
Proof. exact (@lem4867127 A (term565 A u c) (term759 A P c' t' f c x)). Qed.
Lemma lem4867129 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4867130 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term797 A P c' t' f c x) = (term759 A P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867129 A P c' t' f t c x)). Qed.
Lemma lem4867131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867132 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term798 A P c' t' f c x) = (term760 A P c' t' f c x).
Proof. exact (MK_COMB (@lem4867131 A) (@lem4867130 A P c' t' f c x)). Qed.
Lemma lem4867133 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867134 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term794 A u P c' t' f c x) = (term790 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4867133 A u c) (@lem4867132 A P c' t' f c x)). Qed.
Lemma lem4867135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867136 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term799 A u P c' t' f c x) = (term800 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4867135) (@lem4867134 A u P c' t' f c x)). Qed.
Lemma lem4867137 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term796 A P c' t' f c x t) = (term757 A P c' t' f t c x).
Proof. exact (eq_refl (term796 A P c' t' f c x t)). Qed.
Lemma lem4867138 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867139 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term801 A u P c' t' f c x t) = (term802 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4867138 A u c) (@lem4867137 A P c' t' f t c x)). Qed.
Lemma lem4867140 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term803 A u P c' t' f c x) = (term804 A u P c' t' f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867139 A u P c' t' f t c x)). Qed.
Lemma lem4867141 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867142 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term795 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (MK_COMB (@lem4867141 A) (@lem4867140 A u P c' t' f c x)). Qed.
Lemma lem4867143 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : ((term794 A u P c' t' f c x) = (term795 A u P c' t' f c x)) = ((term790 A u P c' t' f c x) = (term805 A u P c' t' f c x)).
Proof. exact (MK_COMB (@lem4867136 A u P c' t' f c x) (@lem4867142 A u P c' t' f c x)). Qed.
Lemma lem4867144 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) (x : A) : (term790 A u P c' t' f c x) = (term805 A u P c' t' f c x).
Proof. exact (EQ_MP (@lem4867143 A u P c' t' f c x) (@lem4867128 A u P c' t' f c x)). Qed.
Lemma lem4867145 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term792 A u P c' t' f c) = (term806 A u P c' t' f c).
Proof. exact (fun_ext (fun x : A => @lem4867144 A u P c' t' f c x)). Qed.
Lemma lem4867146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867147 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term793 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (MK_COMB (@lem4867146 A) (@lem4867145 A u P c' t' f c)). Qed.
Lemma lem4867148 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term778 A u P c' t' f c) = (term807 A u P c' t' f c).
Proof. exact (TRANS (@lem4867124 A u P c' t' f c) (@lem4867147 A u P c' t' f c)). Qed.
Lemma lem4867149 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term780 A u P t' f c) = (term808 A u P t' f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867148 A u P c' t' f c)). Qed.
Lemma lem4867150 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867151 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term781 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (MK_COMB (@lem4867150 A) (@lem4867149 A u P t' f c)). Qed.
Lemma lem4867152 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term765 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4867104 A u P t' f c) (@lem4867151 A u P t' f c)). Qed.
Lemma lem4867153 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) (c : A -> Prop) : (term613 A u P t' f c) = (term809 A u P t' f c).
Proof. exact (TRANS (@lem4867084 A u P t' f c) (@lem4867152 A u P t' f c)). Qed.
Lemma lem4867154 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term614 A u P t' f) = (term810 A u P t' f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4867153 A u P t' f c)). Qed.
Lemma lem4867155 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867156 {A : Type'} (u : type686 A) (P : type686 A) (t' : type667 A) (f : type639 A) : (term615 A u P t' f) = (term811 A u P t' f).
Proof. exact (MK_COMB (@lem4867155 A) (@lem4867154 A u P t' f)). Qed.
Lemma lem4867169 {A : Type'} (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term633 A f t c x) = (term633 A f t c x).
Proof. exact (eq_refl (term633 A f t c x)). Qed.
Lemma lem4867186 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term592 A f t' c x) = (term812 A f t' c x).
Proof. exact (@lem19699 (term584 A f t' c x) (term580 A t' c x) (term566 A c x)). Qed.
Lemma lem4867187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867188 {A : Type'} (f : type639 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term652 A f t' c x) = (term813 A f t' c x).
Proof. exact (MK_COMB (@lem4867187) (@lem4867186 A f t' c x)). Qed.
Lemma lem4867189 {A : Type'} (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term670 A t' f t c x) = (term814 A t' f t c x).
Proof. exact (MK_COMB (@lem4867188 A f t' c x) (@lem4867169 A f t c x)). Qed.
Lemma lem4867198 {A : Type'} (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term690 A f c P c') = (term690 A f c P c').
Proof. exact (eq_refl (term690 A f c P c')). Qed.
Lemma lem4867199 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term716 A P c' t' f t c x) = (term815 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4867198 A f c P c') (@lem4867189 A t' f t c x)). Qed.
Lemma lem4867202 {A : Type'} (f : type639 A) (c : A -> Prop) : (term609 A f c) = (term609 A f c).
Proof. exact (eq_refl (term609 A f c)). Qed.
Lemma lem4867203 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term757 A P c' t' f t c x) = (term816 A P c' t' f t c x).
Proof. exact (MK_COMB (@lem4867202 A f c) (@lem4867199 A P c' t' f t c x)). Qed.
Lemma lem4867206 {A : Type'} (u : type686 A) (c : A -> Prop) : (term612 A u c) = (term612 A u c).
Proof. exact (eq_refl (term612 A u c)). Qed.
Lemma lem4867207 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term817 A u P c' t' f t c x).
Proof. exact (MK_COMB (@lem4867206 A u c) (@lem4867203 A P c' t' f t c x)). Qed.
Lemma lem4867208 {A : Type'} (u : type686 A) (P : type686 A) (c' : A -> Prop) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term818 A u P c' t' f t c x).
Proof. exact (@lem19490 (term608 A f c) (term565 A u c) (term815 A P c' t' f t c x)). Qed.
Lemma lem4867209 {A : Type'} (P : type686 A) (c' : A -> Prop) (u : type686 A) (t' : type667 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term820 A P c' u t' f t c x).
Proof. exact (@lem19490 (term601 A f c P c') (term565 A u c) (term814 A t' f t c x)). Qed.
Lemma lem4867210 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term822 A t' u f t c x).
Proof. exact (@lem19490 (term812 A f t' c x) (term565 A u c) (term633 A f t c x)). Qed.
Lemma lem4867211 {A : Type'} (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term823 A u f t c x) = (term823 A u f t c x).
Proof. exact (eq_refl (term823 A u f t c x)). Qed.
Lemma lem4867218 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term824 A u f t' c x) = (term825 A f u t' c x).
Proof. exact (@lem19490 (term826 A f t' c x) (term565 A u c) (term827 A t' c x)). Qed.
Lemma lem4867219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867220 {A : Type'} (f : type639 A) (u : type686 A) (t' : type667 A) (c : A -> Prop) (x : A) : (term828 A u f t' c x) = (term829 A f u t' c x).
Proof. exact (MK_COMB (@lem4867219) (@lem4867218 A f u t' c x)). Qed.
Lemma lem4867221 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term822 A t' u f t c x) = (term830 A t' u f t c x).
Proof. exact (MK_COMB (@lem4867220 A f u t' c x) (@lem4867211 A u f t c x)). Qed.
Lemma lem4867222 {A : Type'} (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term821 A u t' f t c x) = (term830 A t' u f t c x).
Proof. exact (TRANS (@lem4867210 A t' u f t c x) (@lem4867221 A t' u f t c x)). Qed.
Lemma lem4867225 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) (P : type686 A) (c' : A -> Prop) : (term831 A u f c P c') = (term831 A u f c P c').
Proof. exact (eq_refl (term831 A u f c P c')). Qed.
Lemma lem4867226 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term820 A P c' u t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4867225 A u f c P c') (@lem4867222 A t' u f t c x)). Qed.
Lemma lem4867227 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term819 A u P c' t' f t c x) = (term832 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4867209 A P c' u t' f t c x) (@lem4867226 A P c' t' u f t c x)). Qed.
Lemma lem4867230 {A : Type'} (u : type686 A) (f : type639 A) (c : A -> Prop) : (term833 A u f c) = (term833 A u f c).
Proof. exact (eq_refl (term833 A u f c)). Qed.
Lemma lem4867231 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term818 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (MK_COMB (@lem4867230 A u f c) (@lem4867227 A P c' t' u f t c x)). Qed.
Lemma lem4867232 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term817 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4867208 A u P c' t' f t c x) (@lem4867231 A P c' t' u f t c x)). Qed.
Lemma lem4867233 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (t : A -> Prop) (c : A -> Prop) (x : A) : (term802 A u P c' t' f t c x) = (term834 A P c' t' u f t c x).
Proof. exact (TRANS (@lem4867207 A u P c' t' f t c x) (@lem4867232 A P c' t' u f t c x)). Qed.
Lemma lem4867234 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term804 A u P c' t' f c x) = (term835 A P c' t' u f c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867233 A P c' t' u f t c x)). Qed.
Lemma lem4867235 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867236 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) (x : A) : (term805 A u P c' t' f c x) = (term836 A P c' t' u f c x).
Proof. exact (MK_COMB (@lem4867235 A) (@lem4867234 A P c' t' u f c x)). Qed.
Lemma lem4867237 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term806 A u P c' t' f c) = (term837 A P c' t' u f c).
Proof. exact (fun_ext (fun x : A => @lem4867236 A P c' t' u f c x)). Qed.
Lemma lem4867238 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4867239 {A : Type'} (P : type686 A) (c' : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term807 A u P c' t' f c) = (term838 A P c' t' u f c).
Proof. exact (MK_COMB (@lem4867238 A) (@lem4867237 A P c' t' u f c)). Qed.
Lemma lem4867240 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term808 A u P t' f c) = (term839 A P t' u f c).
Proof. exact (fun_ext (fun c' : A -> Prop => @lem4867239 A P c' t' u f c)). Qed.
Lemma lem4867241 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867242 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (c : A -> Prop) : (term809 A u P t' f c) = (term840 A P t' u f c).
Proof. exact (MK_COMB (@lem4867241 A) (@lem4867240 A P t' u f c)). Qed.
Lemma lem4867243 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term810 A u P t' f) = (term841 A P t' u f).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4867242 A P t' u f c)). Qed.
Lemma lem4867244 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867245 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term811 A u P t' f) = (term842 A P t' u f).
Proof. exact (MK_COMB (@lem4867244 A) (@lem4867243 A P t' u f)). Qed.
Lemma lem4867246 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) : (term615 A u P t' f) = (term842 A P t' u f).
Proof. exact (TRANS (@lem4867156 A u P t' f) (@lem4867245 A P t' u f)). Qed.
Lemma lem4867247 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term842 A P t' u f.
Proof. exact (EQ_MP (@lem4867246 A P t' u f) (@lem4866418 A P t' f u h1)). Qed.
Lemma lem4867265 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term1116 A u f s t x) = (term1116 A u f s t x).
Proof. exact (eq_refl (term1116 A u f s t x)). Qed.
Lemma lem4867266 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1117 A u f s x) = (term1117 A u f s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4867265 A u f s t x)). Qed.
Lemma lem4867267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867268 {A : Type'} (u : type686 A) (f : type639 A) (s : A -> Prop) (x : A) : (term1118 A u f s x) = (term1118 A u f s x).
Proof. exact (MK_COMB (@lem4867267 A) (@lem4867266 A u f s x)). Qed.
Lemma lem4867269 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1119 A u f x) = (term1119 A u f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4867268 A u f s x)). Qed.
Lemma lem4867270 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4867272 {A : Type'} (u : type686 A) (f : type639 A) (x : A) : (term1120 A u f x) = (term1120 A u f x).
Proof. exact (MK_COMB (@lem4867270 A) (@lem4867269 A u f x)). Qed.
Lemma lem4867273 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1120 A u f x.
Proof. exact (EQ_MP (@lem4867272 A u f x) (@lem4866428 A f u s x h1)). Qed.
Lemma lem4867282 {A : Type'} (_60246 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term843 A P t' u f _60246.
Proof. exact (@lem4866824 A P t' f u h1 _60246). Qed.
Lemma lem4867283 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) : (term843 A P t' u f _60246) = (term840 A P t' u f _60246).
Proof. exact (eq_refl (term843 A P t' u f _60246)). Qed.
Lemma lem4867284 {A : Type'} (_60246 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term840 A P t' u f _60246.
Proof. exact (EQ_MP (@lem4867283 A P t' u f _60246) (@lem4867282 A _60246 P t' f u h1)). Qed.
Lemma lem4867285 {A : Type'} (_60246 : A -> Prop) (_60247 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term844 A P t' u f _60246 _60247.
Proof. exact (@lem4867284 A _60246 P t' f u h1 _60247). Qed.
Lemma lem4867286 {A : Type'} (P : type686 A) (_60247 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) : (term844 A P t' u f _60246 _60247) = (term838 A P _60247 t' u f _60246).
Proof. exact (eq_refl (term844 A P t' u f _60246 _60247)). Qed.
Lemma lem4867287 {A : Type'} (_60247 : A -> Prop) (_60246 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term838 A P _60247 t' u f _60246.
Proof. exact (EQ_MP (@lem4867286 A P _60247 t' u f _60246) (@lem4867285 A _60246 _60247 P t' f u h1)). Qed.
Lemma lem4867288 {A : Type'} (_60247 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term845 A P _60247 t' u f _60246 _60248.
Proof. exact (@lem4867287 A _60247 _60246 P t' f u h1 _60248). Qed.
Lemma lem4867289 {A : Type'} (P : type686 A) (_60247 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60248 : A) : (term845 A P _60247 t' u f _60246 _60248) = (term836 A P _60247 t' u f _60246 _60248).
Proof. exact (eq_refl (term845 A P _60247 t' u f _60246 _60248)). Qed.
Lemma lem4867290 {A : Type'} (_60247 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term836 A P _60247 t' u f _60246 _60248.
Proof. exact (EQ_MP (@lem4867289 A P _60247 t' u f _60246 _60248) (@lem4867288 A _60247 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867291 {A : Type'} (_60247 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (_60249 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term846 A P _60247 t' u f _60246 _60248 _60249.
Proof. exact (@lem4867290 A _60247 _60246 _60248 P t' f u h1 _60249). Qed.
Lemma lem4867292 {A : Type'} (P : type686 A) (_60247 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term846 A P _60247 t' u f _60246 _60248 _60249) = (term834 A P _60247 t' u f _60249 _60246 _60248).
Proof. exact (eq_refl (term846 A P _60247 t' u f _60246 _60248 _60249)). Qed.
Lemma lem4867293 {A : Type'} (_60247 : A -> Prop) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term834 A P _60247 t' u f _60249 _60246 _60248.
Proof. exact (EQ_MP (@lem4867292 A P _60247 t' u f _60249 _60246 _60248) (@lem4867291 A _60247 _60246 _60248 _60249 P t' f u h1)). Qed.
Lemma lem4867294 {A : Type'} (_60250 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1132 A u x _60250.
Proof. exact (@lem4866841 A f s t u x h1 _60250). Qed.
Lemma lem4867295 {A : Type'} (u : type686 A) (_60250 : A -> Prop) (x : A) : (term1132 A u x _60250) = (term1123 A u _60250 x).
Proof. exact (eq_refl (term1132 A u x _60250)). Qed.
Lemma lem4867297 {A : Type'} (_60251 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term843 A P t' u f _60251.
Proof. exact (@lem4867247 A P t' f u h1 _60251). Qed.
Lemma lem4867298 {A : Type'} (P : type686 A) (t' : type667 A) (u : type686 A) (f : type639 A) (_60251 : A -> Prop) : (term843 A P t' u f _60251) = (term840 A P t' u f _60251).
Proof. exact (eq_refl (term843 A P t' u f _60251)). Qed.
Lemma lem4867299 {A : Type'} (_60251 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term840 A P t' u f _60251.
Proof. exact (EQ_MP (@lem4867298 A P t' u f _60251) (@lem4867297 A _60251 P t' f u h1)). Qed.
Lemma lem4867300 {A : Type'} (_60251 : A -> Prop) (_60252 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term844 A P t' u f _60251 _60252.
Proof. exact (@lem4867299 A _60251 P t' f u h1 _60252). Qed.
Lemma lem4867301 {A : Type'} (P : type686 A) (_60252 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60251 : A -> Prop) : (term844 A P t' u f _60251 _60252) = (term838 A P _60252 t' u f _60251).
Proof. exact (eq_refl (term844 A P t' u f _60251 _60252)). Qed.
Lemma lem4867302 {A : Type'} (_60252 : A -> Prop) (_60251 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term838 A P _60252 t' u f _60251.
Proof. exact (EQ_MP (@lem4867301 A P _60252 t' u f _60251) (@lem4867300 A _60251 _60252 P t' f u h1)). Qed.
Lemma lem4867303 {A : Type'} (_60252 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term845 A P _60252 t' u f _60251 _60253.
Proof. exact (@lem4867302 A _60252 _60251 P t' f u h1 _60253). Qed.
Lemma lem4867304 {A : Type'} (P : type686 A) (_60252 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60251 : A -> Prop) (_60253 : A) : (term845 A P _60252 t' u f _60251 _60253) = (term836 A P _60252 t' u f _60251 _60253).
Proof. exact (eq_refl (term845 A P _60252 t' u f _60251 _60253)). Qed.
Lemma lem4867305 {A : Type'} (_60252 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term836 A P _60252 t' u f _60251 _60253.
Proof. exact (EQ_MP (@lem4867304 A P _60252 t' u f _60251 _60253) (@lem4867303 A _60252 _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867306 {A : Type'} (_60252 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (_60254 : A -> Prop) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term846 A P _60252 t' u f _60251 _60253 _60254.
Proof. exact (@lem4867305 A _60252 _60251 _60253 P t' f u h1 _60254). Qed.
Lemma lem4867307 {A : Type'} (P : type686 A) (_60252 : A -> Prop) (t' : type667 A) (u : type686 A) (f : type639 A) (_60254 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) : (term846 A P _60252 t' u f _60251 _60253 _60254) = (term834 A P _60252 t' u f _60254 _60251 _60253).
Proof. exact (eq_refl (term846 A P _60252 t' u f _60251 _60253 _60254)). Qed.
Lemma lem4867308 {A : Type'} (_60252 : A -> Prop) (_60254 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term834 A P _60252 t' u f _60254 _60251 _60253.
Proof. exact (EQ_MP (@lem4867307 A P _60252 t' u f _60254 _60251 _60253) (@lem4867306 A _60252 _60251 _60253 _60254 P t' f u h1)). Qed.
Lemma lem4867309 {A : Type'} (_60255 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1133 A u f x _60255.
Proof. exact (@lem4867273 A f u s x h1 _60255). Qed.
Lemma lem4867310 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (x : A) : (term1133 A u f x _60255) = (term1118 A u f _60255 x).
Proof. exact (eq_refl (term1133 A u f x _60255)). Qed.
Lemma lem4867311 {A : Type'} (_60255 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1118 A u f _60255 x.
Proof. exact (EQ_MP (@lem4867310 A u f _60255 x) (@lem4867309 A _60255 f u s x h1)). Qed.
Lemma lem4867312 {A : Type'} (_60255 : A -> Prop) (_60256 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1134 A u f _60255 x _60256.
Proof. exact (@lem4867311 A _60255 f u s x h1 _60256). Qed.
Lemma lem4867313 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1134 A u f _60255 x _60256) = (term1116 A u f _60255 _60256 x).
Proof. exact (eq_refl (term1134 A u f _60255 x _60256)). Qed.
Lemma lem4867314 {A : Type'} (_60255 : A -> Prop) (_60256 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1116 A u f _60255 _60256 x.
Proof. exact (EQ_MP (@lem4867313 A u f _60255 _60256 x) (@lem4867312 A _60255 _60256 f u s x h1)). Qed.
Lemma lem4867315 {A : Type'} (_60247 : A -> Prop) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term832 A P _60247 t' u f _60249 _60246 _60248.
Proof. exact (proj2 (@lem4867293 A _60247 _60249 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867317 {A : Type'} (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term830 A t' u f _60249 _60246 _60248.
Proof. exact (proj2 (@lem4867315 A (@el (A -> Prop)) _60249 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867319 {A : Type'} (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term823 A u f _60249 _60246 _60248.
Proof. exact (proj2 (@lem4867317 A _60249 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867323 {A : Type'} (_60252 : A -> Prop) (_60254 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term832 A P _60252 t' u f _60254 _60251 _60253.
Proof. exact (proj2 (@lem4867308 A _60252 _60254 _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867325 {A : Type'} (_60254 : A -> Prop) (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term830 A t' u f _60254 _60251 _60253.
Proof. exact (proj2 (@lem4867323 A (@el (A -> Prop)) _60254 _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867328 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term825 A f u t' _60251 _60253.
Proof. exact (proj1 (@lem4867325 A (@el (A -> Prop)) _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867338 {A : Type'} (_60250 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1123 A u _60250 x.
Proof. exact (EQ_MP (@lem4867295 A u _60250 x) (@lem4867294 A _60250 f s t u x h1)). Qed.
Lemma lem4867371 {A : Type'} (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term633 A f _60249 _60246 _60248) = (term1135 A f _60249 _60246 _60248).
Proof. exact (@lem4864256 (term568 A f _60246 _60249) (term566 A _60249 _60248) (@I (A -> Prop) _60246 _60248)). Qed.
Lemma lem4867372 {A : Type'} (u : type686 A) (_60246 : A -> Prop) : (term612 A u _60246) = (term612 A u _60246).
Proof. exact (eq_refl (term612 A u _60246)). Qed.
Lemma lem4867375 {A : Type'} (u : type686 A) (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term823 A u f _60249 _60246 _60248) = (term1136 A u f _60249 _60246 _60248).
Proof. exact (MK_COMB (@lem4867372 A u _60246) (@lem4867371 A f _60249 _60246 _60248)). Qed.
Lemma lem4867376 {A : Type'} (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1136 A u f _60249 _60246 _60248.
Proof. exact (EQ_MP (@lem4867375 A u f _60249 _60246 _60248) (@lem4867319 A _60249 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867409 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1116 A u f _60255 _60256 x) = (term1137 A u f _60255 _60256 x).
Proof. exact (@lem4864256 (term565 A u _60255) (term568 A f _60255 _60256) (term566 A _60256 x)). Qed.
Lemma lem4867410 {A : Type'} (_60255 : A -> Prop) (_60256 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1137 A u f _60255 _60256 x.
Proof. exact (EQ_MP (@lem4867409 A u f _60255 _60256 x) (@lem4867314 A _60255 _60256 f u s x h1)). Qed.
Lemma lem4867456 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1138 A u f t' _60251 _60253.
Proof. exact (proj1 (@lem4867328 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867466 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1139 A u t' _60251 _60253.
Proof. exact (proj2 (@lem4867328 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867468 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4866424 A f s t u x h1)). Qed.
Lemma lem4867469 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4867468 A f s t u x h1). Qed.
Lemma lem4867471 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867472 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4867471 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4867473 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4867472 A u s) (@lem4867469 A f s t u x h1)). Qed.
Lemma lem4867475 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4866424 A f s t u x h1)). Qed.
Lemma lem4867476 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4867475 A f s t u x h1). Qed.
Lemma lem4867478 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867479 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4867478 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4867480 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4867479 A u s) (@lem4867476 A f s t u x h1)). Qed.
Lemma lem4867482 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term562 A f s t.
Proof. exact (proj2 (@lem4866424 A f s t u x h1)). Qed.
Lemma lem4867483 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term850 A f s t.
Proof. exact (fun h0 : term568 A f s t => @lem4867482 A f s t u x h1). Qed.
Lemma lem4867485 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867486 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) : (term850 A f s t) = (term562 A f s t).
Proof. exact (@lem4867485 (term562 A f s t)). Qed.
Lemma lem4867487 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term562 A f s t.
Proof. exact (EQ_MP (@lem4867486 A f s t) (@lem4867483 A f s t u x h1)). Qed.
Lemma lem4867489 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4866422 A f s t u x h1)). Qed.
Lemma lem4867490 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1140 A t x.
Proof. exact (fun h0 : term566 A t x => @lem4867489 A f s t u x h1). Qed.
Lemma lem4867492 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867493 {A : Type'} (t : A -> Prop) (x : A) : (term1140 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4867492 (@I (A -> Prop) t x)). Qed.
Lemma lem4867494 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4867493 A t x) (@lem4867490 A f s t u x h1)). Qed.
Lemma lem4867510 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867511 {A : Type'} (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term1135 A f _60249 _60246 _60248) = (term1141 A f _60249 _60246 _60248).
Proof. exact (@lem4867510 (term566 A _60249 _60248) (term568 A f _60246 _60249) (@I (A -> Prop) _60246 _60248)). Qed.
Lemma lem4867525 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867526 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1142 A f _60249 _60246 _60248) = (term1143 A _60248 f _60246 _60249).
Proof. exact (@lem4867525 (@I (A -> Prop) _60246 _60248) (term568 A f _60246 _60249)). Qed.
Lemma lem4867532 {A : Type'} (_60249 : A -> Prop) (_60248 : A) : (term1144 A _60249 _60248) = (term1144 A _60249 _60248).
Proof. exact (eq_refl (term1144 A _60249 _60248)). Qed.
Lemma lem4867533 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1141 A f _60249 _60246 _60248) = (term1145 A _60248 f _60246 _60249).
Proof. exact (MK_COMB (@lem4867532 A _60249 _60248) (@lem4867526 A _60248 f _60246 _60249)). Qed.
Lemma lem4867537 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867538 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1145 A _60248 f _60246 _60249) = (term1146 A _60248 f _60246 _60249).
Proof. exact (@lem4867537 (@I (A -> Prop) _60246 _60248) (term566 A _60249 _60248) (term568 A f _60246 _60249)). Qed.
Lemma lem4867554 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1141 A f _60249 _60246 _60248) = (term1146 A _60248 f _60246 _60249).
Proof. exact (TRANS (@lem4867533 A _60248 f _60246 _60249) (@lem4867538 A _60248 f _60246 _60249)). Qed.
Lemma lem4867555 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1135 A f _60249 _60246 _60248) = (term1146 A _60248 f _60246 _60249).
Proof. exact (TRANS (@lem4867511 A f _60249 _60246 _60248) (@lem4867554 A _60248 f _60246 _60249)). Qed.
Lemma lem4867556 {A : Type'} (u : type686 A) (_60246 : A -> Prop) : (term612 A u _60246) = (term612 A u _60246).
Proof. exact (eq_refl (term612 A u _60246)). Qed.
Lemma lem4867557 {A : Type'} (u : type686 A) (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1136 A u f _60249 _60246 _60248) = (term1147 A u _60248 f _60246 _60249).
Proof. exact (MK_COMB (@lem4867556 A u _60246) (@lem4867555 A _60248 f _60246 _60249)). Qed.
Lemma lem4867561 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867562 {A : Type'} (u : type686 A) (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1147 A u _60248 f _60246 _60249) = (term1148 A u _60248 f _60246 _60249).
Proof. exact (@lem4867561 (@I (A -> Prop) _60246 _60248) (term565 A u _60246) (term1149 A _60248 f _60246 _60249)). Qed.
Lemma lem4867576 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867577 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1150 A u _60248 f _60246 _60249) = (term1151 A _60248 u f _60246 _60249).
Proof. exact (@lem4867576 (term566 A _60249 _60248) (term565 A u _60246) (term568 A f _60246 _60249)). Qed.
Lemma lem4867593 {A : Type'} (_60246 : A -> Prop) (_60248 : A) : (term1152 A _60246 _60248) = (term1152 A _60246 _60248).
Proof. exact (eq_refl (term1152 A _60246 _60248)). Qed.
Lemma lem4867594 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1148 A u _60248 f _60246 _60249) = (term1153 A _60248 u f _60246 _60249).
Proof. exact (MK_COMB (@lem4867593 A _60246 _60248) (@lem4867577 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867605 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1147 A u _60248 f _60246 _60249) = (term1153 A _60248 u f _60246 _60249).
Proof. exact (TRANS (@lem4867562 A u _60248 f _60246 _60249) (@lem4867594 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867606 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1136 A u f _60249 _60246 _60248) = (term1153 A _60248 u f _60246 _60249).
Proof. exact (TRANS (@lem4867557 A u _60248 f _60246 _60249) (@lem4867605 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867608 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1154 A u f _60249 _60246 _60248) = (term1155 A _60248 u f _60246 _60249).
Proof. exact (MK_COMB (@lem4867607) (@lem4867606 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867633 {A : Type'} (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term571 A f _60246 _60249 _60248) = (term1149 A _60248 f _60246 _60249).
Proof. exact (@lem4867632 (term566 A _60249 _60248) (term568 A f _60246 _60249)). Qed.
Lemma lem4867639 {A : Type'} (u : type686 A) (_60246 : A -> Prop) : (term612 A u _60246) = (term612 A u _60246).
Proof. exact (eq_refl (term612 A u _60246)). Qed.
Lemma lem4867640 {A : Type'} (u : type686 A) (_60248 : A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1137 A u f _60246 _60249 _60248) = (term1150 A u _60248 f _60246 _60249).
Proof. exact (MK_COMB (@lem4867639 A u _60246) (@lem4867633 A _60248 f _60246 _60249)). Qed.
Lemma lem4867644 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867645 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1150 A u _60248 f _60246 _60249) = (term1151 A _60248 u f _60246 _60249).
Proof. exact (@lem4867644 (term566 A _60249 _60248) (term565 A u _60246) (term568 A f _60246 _60249)). Qed.
Lemma lem4867661 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1137 A u f _60246 _60249 _60248) = (term1151 A _60248 u f _60246 _60249).
Proof. exact (TRANS (@lem4867640 A u _60248 f _60246 _60249) (@lem4867645 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867662 {A : Type'} (_60246 : A -> Prop) (_60248 : A) : (term1152 A _60246 _60248) = (term1152 A _60246 _60248).
Proof. exact (eq_refl (term1152 A _60246 _60248)). Qed.
Lemma lem4867663 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1156 A u f _60246 _60249 _60248) = (term1153 A _60248 u f _60246 _60249).
Proof. exact (MK_COMB (@lem4867662 A _60246 _60248) (@lem4867661 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867674 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : ((term1136 A u f _60249 _60246 _60248) = (term1156 A u f _60246 _60249 _60248)) = ((term1153 A _60248 u f _60246 _60249) = (term1153 A _60248 u f _60246 _60249)).
Proof. exact (MK_COMB (@lem4867608 A _60248 u f _60246 _60249) (@lem4867663 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4867677 (x : Prop) : (x = x) = True.
Proof. exact (@lem4867676 Prop x). Qed.
Lemma lem4867678 {A : Type'} (_60248 : A) (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : ((term1153 A _60248 u f _60246 _60249) = (term1153 A _60248 u f _60246 _60249)) = True.
Proof. exact (@lem4867677 (term1153 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867679 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : ((term1136 A u f _60249 _60246 _60248) = (term1156 A u f _60246 _60249 _60248)) = True.
Proof. exact (TRANS (@lem4867674 A _60248 u f _60246 _60249) (@lem4867678 A _60248 u f _60246 _60249)). Qed.
Lemma lem4867680 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : True = ((term1136 A u f _60249 _60246 _60248) = (term1156 A u f _60246 _60249 _60248)).
Proof. exact (SYM (@lem4867679 A u f _60246 _60249 _60248)). Qed.
Lemma lem4867681 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1136 A u f _60249 _60246 _60248) = (term1156 A u f _60246 _60249 _60248).
Proof. exact (EQ_MP (@lem4867680 A u f _60246 _60249 _60248) (@lem0)). Qed.
Lemma lem4867682 {A : Type'} (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1156 A u f _60246 _60249 _60248.
Proof. exact (EQ_MP (@lem4867681 A u f _60246 _60249 _60248) (@lem4867376 A _60249 _60246 _60248 P t' f u h1)). Qed.
Lemma lem4867684 (b : Prop) (a : Prop) : (a \/ b) = (term857 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4867685 {A : Type'} (u : type686 A) (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term1156 A u f _60246 _60249 _60248) = (term1157 A u f _60249 _60246 _60248).
Proof. exact (@lem4867684 (term1137 A u f _60246 _60249 _60248) (@I (A -> Prop) _60246 _60248)). Qed.
Lemma lem4867687 (a : Prop) (b : Prop) : (term860 a b) = (term861 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4867688 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1158 A u f _60246 _60249 _60248) = (term1159 A u f _60246 _60249 _60248).
Proof. exact (@lem4867687 (term565 A u _60246) (term571 A f _60246 _60249 _60248)). Qed.
Lemma lem4867690 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867691 {A : Type'} (u : type686 A) (_60246 : A -> Prop) : (term864 A u _60246) = (@I ((A -> Prop) -> Prop) u _60246).
Proof. exact (@lem4867690 (@I ((A -> Prop) -> Prop) u _60246)). Qed.
Lemma lem4867692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867693 {A : Type'} (u : type686 A) (_60246 : A -> Prop) : (term865 A u _60246) = (term563 A u _60246).
Proof. exact (MK_COMB (@lem4867692) (@lem4867691 A u _60246)). Qed.
Lemma lem4867695 (a : Prop) (b : Prop) : (term860 a b) = (term861 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4867696 {A : Type'} (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1160 A f _60246 _60249 _60248) = (term1161 A f _60246 _60249 _60248).
Proof. exact (@lem4867695 (term568 A f _60246 _60249) (term566 A _60249 _60248)). Qed.
Lemma lem4867698 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867699 {A : Type'} (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term866 A f _60246 _60249) = (term562 A f _60246 _60249).
Proof. exact (@lem4867698 (term562 A f _60246 _60249)). Qed.
Lemma lem4867700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867701 {A : Type'} (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) : (term1162 A f _60246 _60249) = (term1163 A f _60246 _60249).
Proof. exact (MK_COMB (@lem4867700) (@lem4867699 A f _60246 _60249)). Qed.
Lemma lem4867703 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867704 {A : Type'} (_60249 : A -> Prop) (_60248 : A) : (term1164 A _60249 _60248) = (@I (A -> Prop) _60249 _60248).
Proof. exact (@lem4867703 (@I (A -> Prop) _60249 _60248)). Qed.
Lemma lem4867705 {A : Type'} (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1161 A f _60246 _60249 _60248) = (term1165 A f _60246 _60249 _60248).
Proof. exact (MK_COMB (@lem4867701 A f _60246 _60249) (@lem4867704 A _60249 _60248)). Qed.
Lemma lem4867706 {A : Type'} (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1160 A f _60246 _60249 _60248) = (term1165 A f _60246 _60249 _60248).
Proof. exact (TRANS (@lem4867696 A f _60246 _60249 _60248) (@lem4867705 A f _60246 _60249 _60248)). Qed.
Lemma lem4867707 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1159 A u f _60246 _60249 _60248) = (term1166 A u f _60246 _60249 _60248).
Proof. exact (MK_COMB (@lem4867693 A u _60246) (@lem4867706 A f _60246 _60249 _60248)). Qed.
Lemma lem4867708 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1158 A u f _60246 _60249 _60248) = (term1166 A u f _60246 _60249 _60248).
Proof. exact (TRANS (@lem4867688 A u f _60246 _60249 _60248) (@lem4867707 A u f _60246 _60249 _60248)). Qed.
Lemma lem4867709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4867710 {A : Type'} (u : type686 A) (f : type639 A) (_60246 : A -> Prop) (_60249 : A -> Prop) (_60248 : A) : (term1167 A u f _60246 _60249 _60248) = (term1168 A u f _60246 _60249 _60248).
Proof. exact (MK_COMB (@lem4867709) (@lem4867708 A u f _60246 _60249 _60248)). Qed.
Lemma lem4867711 {A : Type'} (_60246 : A -> Prop) (_60248 : A) : (@I (A -> Prop) _60246 _60248) = (@I (A -> Prop) _60246 _60248).
Proof. exact (eq_refl (@I (A -> Prop) _60246 _60248)). Qed.
Lemma lem4867712 {A : Type'} (u : type686 A) (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term1157 A u f _60249 _60246 _60248) = (term1169 A u f _60249 _60246 _60248).
Proof. exact (MK_COMB (@lem4867710 A u f _60246 _60249 _60248) (@lem4867711 A _60246 _60248)). Qed.
Lemma lem4867713 {A : Type'} (u : type686 A) (f : type639 A) (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) : (term1156 A u f _60246 _60249 _60248) = (term1169 A u f _60249 _60246 _60248).
Proof. exact (TRANS (@lem4867685 A u f _60249 _60246 _60248) (@lem4867712 A u f _60249 _60246 _60248)). Qed.
Lemma lem4867715 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1165 A f s t x.
Proof. exact (conj (@lem4867487 A f s t u x h1) (@lem4867494 A f s t u x h1)). Qed.
Lemma lem4867716 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1166 A u f s t x.
Proof. exact (conj (@lem4867480 A f s t u x h1) (@lem4867715 A f s t u x h1)). Qed.
Lemma lem4867718 {A : Type'} (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1169 A u f _60249 _60246 _60248.
Proof. exact (EQ_MP (@lem4867713 A u f _60249 _60246 _60248) (@lem4867682 A _60246 _60249 _60248 P t' f u h1)). Qed.
Lemma lem4867719 {A : Type'} (_60249 : A -> Prop) (_60246 : A -> Prop) (_60248 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1169 A u f _60249 _60246 _60248.
Proof. exact (@lem4867718 A _60249 _60246 _60248 P t' f u h1). Qed.
Lemma lem4867720 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1169 A u f t s x.
Proof. exact (@lem4867719 A t s x P t' f u h1). Qed.
Lemma lem4867723 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : @I (A -> Prop) s x.
Proof. exact (@lem4867720 A t s x P t' f u h1 (@lem4867716 A f s t u x h2)). Qed.
Lemma lem4867724 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : term1140 A s x.
Proof. exact (fun h0 : term566 A s x => @lem4867723 A P t' f s t u x h1 h2). Qed.
Lemma lem4867726 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867727 {A : Type'} (s : A -> Prop) (x : A) : (term1140 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4867726 (@I (A -> Prop) s x)). Qed.
Lemma lem4867728 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4867727 A s x) (@lem4867724 A P t' f s t u x h1 h2)). Qed.
Lemma lem4867730 (a : Prop) (b : Prop) : (term1170 a b) = (term1171 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4867731 {A : Type'} (u : type686 A) (_60250 : A -> Prop) (x : A) : (term1123 A u _60250 x) = (term1172 A u _60250 x).
Proof. exact (@lem4867730 (@I ((A -> Prop) -> Prop) u _60250) (@I (A -> Prop) _60250 x)). Qed.
Lemma lem4867733 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4867734 {A : Type'} (u : type686 A) (_60250 : A -> Prop) (x : A) : (term1172 A u _60250 x) = (term1173 A u _60250 x).
Proof. exact (@lem4867733 (term1114 A u _60250 x)). Qed.
Lemma lem4867735 {A : Type'} (u : type686 A) (_60250 : A -> Prop) (x : A) : (term1123 A u _60250 x) = (term1173 A u _60250 x).
Proof. exact (TRANS (@lem4867731 A u _60250 x) (@lem4867734 A u _60250 x)). Qed.
Lemma lem4867737 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : term1114 A u s x.
Proof. exact (conj (@lem4867473 A f s t u x h2) (@lem4867728 A P t' f s t u x h1 h2)). Qed.
Lemma lem4867739 {A : Type'} (_60250 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1173 A u _60250 x.
Proof. exact (EQ_MP (@lem4867735 A u _60250 x) (@lem4867338 A _60250 f s t u x h1)). Qed.
Lemma lem4867740 {A : Type'} (_60250 : A -> Prop) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1173 A u _60250 x.
Proof. exact (@lem4867739 A _60250 f s t u x h1). Qed.
Lemma lem4867741 {A : Type'} (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term1129 A f s t u x) : term1173 A u s x.
Proof. exact (@lem4867740 A s f s t u x h1). Qed.
Lemma lem4867744 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : False.
Proof. exact (@lem4867741 A f s t u x h2 (@lem4867737 A P t' f s t u x h1 h2)). Qed.
Lemma lem4867745 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : term871.
Proof. exact (fun h0 : ~ False => @lem4867744 A P t' f s t u x h1 h2). Qed.
Lemma lem4867747 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867748 : term871 = False.
Proof. exact (@lem4867747 False). Qed.
Lemma lem4867749 {A : Type'} (P : type686 A) (t' : type667 A) (f : type639 A) (s : A -> Prop) (t : A -> Prop) (u : type686 A) (x : A) (h1 : term558 A P t' f u) (h2 : term1129 A f s t u x) : False.
Proof. exact (EQ_MP (@lem4867748) (@lem4867745 A P t' f s t u x h1 h2)). Qed.
Lemma lem4867751 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4866427 A f u s x h1)). Qed.
Lemma lem4867752 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4867751 A f u s x h1). Qed.
Lemma lem4867754 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867755 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4867754 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4867756 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4867755 A u s) (@lem4867752 A f u s x h1)). Qed.
Lemma lem4867758 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4866427 A f u s x h1)). Qed.
Lemma lem4867759 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4867758 A f u s x h1). Qed.
Lemma lem4867761 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867762 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4867761 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4867763 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4867762 A u s) (@lem4867759 A f u s x h1)). Qed.
Lemma lem4867765 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4866427 A f u s x h1)). Qed.
Lemma lem4867766 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1140 A s x.
Proof. exact (fun h0 : term566 A s x => @lem4867765 A f u s x h1). Qed.
Lemma lem4867768 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867769 {A : Type'} (s : A -> Prop) (x : A) : (term1140 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4867768 (@I (A -> Prop) s x)). Qed.
Lemma lem4867770 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4867769 A s x) (@lem4867766 A f u s x h1)). Qed.
Lemma lem4867776 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867777 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1138 A u f t' _60251 _60253) = (term1174 A f t' u _60251 _60253).
Proof. exact (@lem4867776 (term584 A f t' _60251 _60253) (term565 A u _60251) (term566 A _60251 _60253)). Qed.
Lemma lem4867791 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867792 {A : Type'} (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1123 A u _60251 _60253) = (term1175 A _60253 u _60251).
Proof. exact (@lem4867791 (term566 A _60251 _60253) (term565 A u _60251)). Qed.
Lemma lem4867798 {A : Type'} (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1176 A f t' _60251 _60253) = (term1176 A f t' _60251 _60253).
Proof. exact (eq_refl (term1176 A f t' _60251 _60253)). Qed.
Lemma lem4867799 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1174 A f t' u _60251 _60253) = (term1177 A f t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867798 A f t' _60251 _60253) (@lem4867792 A _60253 u _60251)). Qed.
Lemma lem4867810 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1138 A u f t' _60251 _60253) = (term1177 A f t' _60253 u _60251).
Proof. exact (TRANS (@lem4867777 A f t' u _60251 _60253) (@lem4867799 A f t' _60253 u _60251)). Qed.
Lemma lem4867811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867812 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1178 A u f t' _60251 _60253) = (term1179 A f t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867811) (@lem4867810 A f t' _60253 u _60251)). Qed.
Lemma lem4867826 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867827 {A : Type'} (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1123 A u _60251 _60253) = (term1175 A _60253 u _60251).
Proof. exact (@lem4867826 (term566 A _60251 _60253) (term565 A u _60251)). Qed.
Lemma lem4867833 {A : Type'} (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1176 A f t' _60251 _60253) = (term1176 A f t' _60251 _60253).
Proof. exact (eq_refl (term1176 A f t' _60251 _60253)). Qed.
Lemma lem4867834 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1174 A f t' u _60251 _60253) = (term1177 A f t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867833 A f t' _60251 _60253) (@lem4867827 A _60253 u _60251)). Qed.
Lemma lem4867845 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : ((term1138 A u f t' _60251 _60253) = (term1174 A f t' u _60251 _60253)) = ((term1177 A f t' _60253 u _60251) = (term1177 A f t' _60253 u _60251)).
Proof. exact (MK_COMB (@lem4867812 A f t' _60253 u _60251) (@lem4867834 A f t' _60253 u _60251)). Qed.
Lemma lem4867847 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4867848 (x : Prop) : (x = x) = True.
Proof. exact (@lem4867847 Prop x). Qed.
Lemma lem4867849 {A : Type'} (f : type639 A) (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : ((term1177 A f t' _60253 u _60251) = (term1177 A f t' _60253 u _60251)) = True.
Proof. exact (@lem4867848 (term1177 A f t' _60253 u _60251)). Qed.
Lemma lem4867850 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : ((term1138 A u f t' _60251 _60253) = (term1174 A f t' u _60251 _60253)) = True.
Proof. exact (TRANS (@lem4867845 A f t' _60253 u _60251) (@lem4867849 A f t' _60253 u _60251)). Qed.
Lemma lem4867851 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : True = ((term1138 A u f t' _60251 _60253) = (term1174 A f t' u _60251 _60253)).
Proof. exact (SYM (@lem4867850 A f t' u _60251 _60253)). Qed.
Lemma lem4867852 {A : Type'} (f : type639 A) (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1138 A u f t' _60251 _60253) = (term1174 A f t' u _60251 _60253).
Proof. exact (EQ_MP (@lem4867851 A f t' u _60251 _60253) (@lem0)). Qed.
Lemma lem4867853 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1174 A f t' u _60251 _60253.
Proof. exact (EQ_MP (@lem4867852 A f t' u _60251 _60253) (@lem4867456 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867855 (b : Prop) (a : Prop) : (a \/ b) = (term857 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4867856 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1174 A f t' u _60251 _60253) = (term1180 A u f t' _60251 _60253).
Proof. exact (@lem4867855 (term1123 A u _60251 _60253) (term584 A f t' _60251 _60253)). Qed.
Lemma lem4867858 (a : Prop) (b : Prop) : (term860 a b) = (term861 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4867859 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1181 A u _60251 _60253) = (term1182 A u _60251 _60253).
Proof. exact (@lem4867858 (term565 A u _60251) (term566 A _60251 _60253)). Qed.
Lemma lem4867861 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867862 {A : Type'} (u : type686 A) (_60251 : A -> Prop) : (term864 A u _60251) = (@I ((A -> Prop) -> Prop) u _60251).
Proof. exact (@lem4867861 (@I ((A -> Prop) -> Prop) u _60251)). Qed.
Lemma lem4867863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867864 {A : Type'} (u : type686 A) (_60251 : A -> Prop) : (term865 A u _60251) = (term563 A u _60251).
Proof. exact (MK_COMB (@lem4867863) (@lem4867862 A u _60251)). Qed.
Lemma lem4867866 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867867 {A : Type'} (_60251 : A -> Prop) (_60253 : A) : (term1164 A _60251 _60253) = (@I (A -> Prop) _60251 _60253).
Proof. exact (@lem4867866 (@I (A -> Prop) _60251 _60253)). Qed.
Lemma lem4867868 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1182 A u _60251 _60253) = (term1114 A u _60251 _60253).
Proof. exact (MK_COMB (@lem4867864 A u _60251) (@lem4867867 A _60251 _60253)). Qed.
Lemma lem4867869 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1181 A u _60251 _60253) = (term1114 A u _60251 _60253).
Proof. exact (TRANS (@lem4867859 A u _60251 _60253) (@lem4867868 A u _60251 _60253)). Qed.
Lemma lem4867870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4867871 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1183 A u _60251 _60253) = (term1184 A u _60251 _60253).
Proof. exact (MK_COMB (@lem4867870) (@lem4867869 A u _60251 _60253)). Qed.
Lemma lem4867872 {A : Type'} (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term584 A f t' _60251 _60253) = (term584 A f t' _60251 _60253).
Proof. exact (eq_refl (term584 A f t' _60251 _60253)). Qed.
Lemma lem4867873 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1180 A u f t' _60251 _60253) = (term1185 A u f t' _60251 _60253).
Proof. exact (MK_COMB (@lem4867871 A u _60251 _60253) (@lem4867872 A f t' _60251 _60253)). Qed.
Lemma lem4867874 {A : Type'} (u : type686 A) (f : type639 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1174 A f t' u _60251 _60253) = (term1185 A u f t' _60251 _60253).
Proof. exact (TRANS (@lem4867856 A u f t' _60251 _60253) (@lem4867873 A u f t' _60251 _60253)). Qed.
Lemma lem4867876 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1114 A u s x.
Proof. exact (conj (@lem4867763 A f u s x h1) (@lem4867770 A f u s x h1)). Qed.
Lemma lem4867878 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1185 A u f t' _60251 _60253.
Proof. exact (EQ_MP (@lem4867874 A u f t' _60251 _60253) (@lem4867853 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867879 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1185 A u f t' _60251 _60253.
Proof. exact (@lem4867878 A _60251 _60253 P t' f u h1). Qed.
Lemma lem4867880 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1185 A u f t' s x.
Proof. exact (@lem4867879 A s x P t' f u h1). Qed.
Lemma lem4867883 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term584 A f t' s x.
Proof. exact (@lem4867880 A s x P t' f u h2 (@lem4867876 A f u s x h1)). Qed.
Lemma lem4867884 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term1186 A f t' s x.
Proof. exact (fun h0 : term1187 A f t' s x => @lem4867883 A s x P t' f u h1 h2). Qed.
Lemma lem4867886 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867887 {A : Type'} (f : type639 A) (t' : type667 A) (s : A -> Prop) (x : A) : (term1186 A f t' s x) = (term584 A f t' s x).
Proof. exact (@lem4867886 (term584 A f t' s x)). Qed.
Lemma lem4867888 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term584 A f t' s x.
Proof. exact (EQ_MP (@lem4867887 A f t' s x) (@lem4867884 A s x P t' f u h1 h2)). Qed.
Lemma lem4867890 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (proj1 (@lem4866427 A f u s x h1)). Qed.
Lemma lem4867891 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term848 A u s.
Proof. exact (fun h0 : term565 A u s => @lem4867890 A f u s x h1). Qed.
Lemma lem4867893 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867894 {A : Type'} (u : type686 A) (s : A -> Prop) : (term848 A u s) = (@I ((A -> Prop) -> Prop) u s).
Proof. exact (@lem4867893 (@I ((A -> Prop) -> Prop) u s)). Qed.
Lemma lem4867895 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I ((A -> Prop) -> Prop) u s.
Proof. exact (EQ_MP (@lem4867894 A u s) (@lem4867891 A f u s x h1)). Qed.
Lemma lem4867897 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4866427 A f u s x h1)). Qed.
Lemma lem4867898 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1140 A s x.
Proof. exact (fun h0 : term566 A s x => @lem4867897 A f u s x h1). Qed.
Lemma lem4867900 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4867901 {A : Type'} (s : A -> Prop) (x : A) : (term1140 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4867900 (@I (A -> Prop) s x)). Qed.
Lemma lem4867902 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4867901 A s x) (@lem4867898 A f u s x h1)). Qed.
Lemma lem4867908 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4867909 {A : Type'} (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1139 A u t' _60251 _60253) = (term1188 A t' u _60251 _60253).
Proof. exact (@lem4867908 (term580 A t' _60251 _60253) (term565 A u _60251) (term566 A _60251 _60253)). Qed.
Lemma lem4867923 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867924 {A : Type'} (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1123 A u _60251 _60253) = (term1175 A _60253 u _60251).
Proof. exact (@lem4867923 (term566 A _60251 _60253) (term565 A u _60251)). Qed.
Lemma lem4867930 {A : Type'} (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1189 A t' _60251 _60253) = (term1189 A t' _60251 _60253).
Proof. exact (eq_refl (term1189 A t' _60251 _60253)). Qed.
Lemma lem4867931 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1188 A t' u _60251 _60253) = (term1190 A t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867930 A t' _60251 _60253) (@lem4867924 A _60253 u _60251)). Qed.
Lemma lem4867942 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1139 A u t' _60251 _60253) = (term1190 A t' _60253 u _60251).
Proof. exact (TRANS (@lem4867909 A t' u _60251 _60253) (@lem4867931 A t' _60253 u _60251)). Qed.
Lemma lem4867943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4867944 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1191 A u t' _60251 _60253) = (term1192 A t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867943) (@lem4867942 A t' _60253 u _60251)). Qed.
Lemma lem4867958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4867959 {A : Type'} (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1123 A u _60251 _60253) = (term1175 A _60253 u _60251).
Proof. exact (@lem4867958 (term566 A _60251 _60253) (term565 A u _60251)). Qed.
Lemma lem4867965 {A : Type'} (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1189 A t' _60251 _60253) = (term1189 A t' _60251 _60253).
Proof. exact (eq_refl (term1189 A t' _60251 _60253)). Qed.
Lemma lem4867966 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : (term1188 A t' u _60251 _60253) = (term1190 A t' _60253 u _60251).
Proof. exact (MK_COMB (@lem4867965 A t' _60251 _60253) (@lem4867959 A _60253 u _60251)). Qed.
Lemma lem4867977 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : ((term1139 A u t' _60251 _60253) = (term1188 A t' u _60251 _60253)) = ((term1190 A t' _60253 u _60251) = (term1190 A t' _60253 u _60251)).
Proof. exact (MK_COMB (@lem4867944 A t' _60253 u _60251) (@lem4867966 A t' _60253 u _60251)). Qed.
Lemma lem4867979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4867980 (x : Prop) : (x = x) = True.
Proof. exact (@lem4867979 Prop x). Qed.
Lemma lem4867981 {A : Type'} (t' : type667 A) (_60253 : A) (u : type686 A) (_60251 : A -> Prop) : ((term1190 A t' _60253 u _60251) = (term1190 A t' _60253 u _60251)) = True.
Proof. exact (@lem4867980 (term1190 A t' _60253 u _60251)). Qed.
Lemma lem4867982 {A : Type'} (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : ((term1139 A u t' _60251 _60253) = (term1188 A t' u _60251 _60253)) = True.
Proof. exact (TRANS (@lem4867977 A t' _60253 u _60251) (@lem4867981 A t' _60253 u _60251)). Qed.
Lemma lem4867983 {A : Type'} (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : True = ((term1139 A u t' _60251 _60253) = (term1188 A t' u _60251 _60253)).
Proof. exact (SYM (@lem4867982 A t' u _60251 _60253)). Qed.
Lemma lem4867984 {A : Type'} (t' : type667 A) (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1139 A u t' _60251 _60253) = (term1188 A t' u _60251 _60253).
Proof. exact (EQ_MP (@lem4867983 A t' u _60251 _60253) (@lem0)). Qed.
Lemma lem4867985 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1188 A t' u _60251 _60253.
Proof. exact (EQ_MP (@lem4867984 A t' u _60251 _60253) (@lem4867466 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4867987 (b : Prop) (a : Prop) : (a \/ b) = (term857 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4867988 {A : Type'} (u : type686 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1188 A t' u _60251 _60253) = (term1193 A u t' _60251 _60253).
Proof. exact (@lem4867987 (term1123 A u _60251 _60253) (term580 A t' _60251 _60253)). Qed.
Lemma lem4867990 (a : Prop) (b : Prop) : (term860 a b) = (term861 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4867991 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1181 A u _60251 _60253) = (term1182 A u _60251 _60253).
Proof. exact (@lem4867990 (term565 A u _60251) (term566 A _60251 _60253)). Qed.
Lemma lem4867993 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867994 {A : Type'} (u : type686 A) (_60251 : A -> Prop) : (term864 A u _60251) = (@I ((A -> Prop) -> Prop) u _60251).
Proof. exact (@lem4867993 (@I ((A -> Prop) -> Prop) u _60251)). Qed.
Lemma lem4867995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4867996 {A : Type'} (u : type686 A) (_60251 : A -> Prop) : (term865 A u _60251) = (term563 A u _60251).
Proof. exact (MK_COMB (@lem4867995) (@lem4867994 A u _60251)). Qed.
Lemma lem4867998 (a : Prop) : (term326 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4867999 {A : Type'} (_60251 : A -> Prop) (_60253 : A) : (term1164 A _60251 _60253) = (@I (A -> Prop) _60251 _60253).
Proof. exact (@lem4867998 (@I (A -> Prop) _60251 _60253)). Qed.
Lemma lem4868000 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1182 A u _60251 _60253) = (term1114 A u _60251 _60253).
Proof. exact (MK_COMB (@lem4867996 A u _60251) (@lem4867999 A _60251 _60253)). Qed.
Lemma lem4868001 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1181 A u _60251 _60253) = (term1114 A u _60251 _60253).
Proof. exact (TRANS (@lem4867991 A u _60251 _60253) (@lem4868000 A u _60251 _60253)). Qed.
Lemma lem4868002 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4868003 {A : Type'} (u : type686 A) (_60251 : A -> Prop) (_60253 : A) : (term1183 A u _60251 _60253) = (term1184 A u _60251 _60253).
Proof. exact (MK_COMB (@lem4868002) (@lem4868001 A u _60251 _60253)). Qed.
Lemma lem4868004 {A : Type'} (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term580 A t' _60251 _60253) = (term580 A t' _60251 _60253).
Proof. exact (eq_refl (term580 A t' _60251 _60253)). Qed.
Lemma lem4868005 {A : Type'} (u : type686 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1193 A u t' _60251 _60253) = (term1194 A u t' _60251 _60253).
Proof. exact (MK_COMB (@lem4868003 A u _60251 _60253) (@lem4868004 A t' _60251 _60253)). Qed.
Lemma lem4868006 {A : Type'} (u : type686 A) (t' : type667 A) (_60251 : A -> Prop) (_60253 : A) : (term1188 A t' u _60251 _60253) = (term1194 A u t' _60251 _60253).
Proof. exact (TRANS (@lem4867988 A u t' _60251 _60253) (@lem4868005 A u t' _60251 _60253)). Qed.
Lemma lem4868008 {A : Type'} (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1114 A u s x.
Proof. exact (conj (@lem4867895 A f u s x h1) (@lem4867902 A f u s x h1)). Qed.
Lemma lem4868010 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1194 A u t' _60251 _60253.
Proof. exact (EQ_MP (@lem4868006 A u t' _60251 _60253) (@lem4867985 A _60251 _60253 P t' f u h1)). Qed.
Lemma lem4868011 {A : Type'} (_60251 : A -> Prop) (_60253 : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1194 A u t' _60251 _60253.
Proof. exact (@lem4868010 A _60251 _60253 P t' f u h1). Qed.
Lemma lem4868012 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term558 A P t' f u) : term1194 A u t' s x.
Proof. exact (@lem4868011 A s x P t' f u h1). Qed.
Lemma lem4868015 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term580 A t' s x.
Proof. exact (@lem4868012 A s x P t' f u h2 (@lem4868008 A f u s x h1)). Qed.
Lemma lem4868016 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term1195 A t' s x.
Proof. exact (fun h0 : term1196 A t' s x => @lem4868015 A s x P t' f u h1 h2). Qed.
Lemma lem4868018 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4868019 {A : Type'} (t' : type667 A) (s : A -> Prop) (x : A) : (term1195 A t' s x) = (term580 A t' s x).
Proof. exact (@lem4868018 (term580 A t' s x)). Qed.
Lemma lem4868020 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term580 A t' s x.
Proof. exact (EQ_MP (@lem4868019 A t' s x) (@lem4868016 A s x P t' f u h1 h2)). Qed.
Lemma lem4868022 (a : Prop) (b : Prop) : (term1170 a b) = (term1171 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4868023 {A : Type'} (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term571 A f _60255 _60256 x) = (term1197 A f _60255 _60256 x).
Proof. exact (@lem4868022 (term562 A f _60255 _60256) (@I (A -> Prop) _60256 x)). Qed.
Lemma lem4868024 {A : Type'} (u : type686 A) (_60255 : A -> Prop) : (term612 A u _60255) = (term612 A u _60255).
Proof. exact (eq_refl (term612 A u _60255)). Qed.
Lemma lem4868025 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1137 A u f _60255 _60256 x) = (term1198 A u f _60255 _60256 x).
Proof. exact (MK_COMB (@lem4868024 A u _60255) (@lem4868023 A f _60255 _60256 x)). Qed.
Lemma lem4868027 (a : Prop) (b : Prop) : (term1170 a b) = (term1171 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4868028 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1198 A u f _60255 _60256 x) = (term1199 A u f _60255 _60256 x).
Proof. exact (@lem4868027 (@I ((A -> Prop) -> Prop) u _60255) (term1165 A f _60255 _60256 x)). Qed.
Lemma lem4868029 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1137 A u f _60255 _60256 x) = (term1199 A u f _60255 _60256 x).
Proof. exact (TRANS (@lem4868025 A u f _60255 _60256 x) (@lem4868028 A u f _60255 _60256 x)). Qed.
Lemma lem4868031 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4868032 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1199 A u f _60255 _60256 x) = (term1200 A u f _60255 _60256 x).
Proof. exact (@lem4868031 (term1166 A u f _60255 _60256 x)). Qed.
Lemma lem4868033 {A : Type'} (u : type686 A) (f : type639 A) (_60255 : A -> Prop) (_60256 : A -> Prop) (x : A) : (term1137 A u f _60255 _60256 x) = (term1200 A u f _60255 _60256 x).
Proof. exact (TRANS (@lem4868029 A u f _60255 _60256 x) (@lem4868032 A u f _60255 _60256 x)). Qed.
Lemma lem4868035 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term588 A f t' s x.
Proof. exact (conj (@lem4867888 A s x P t' f u h1 h2) (@lem4868020 A s x P t' f u h1 h2)). Qed.
Lemma lem4868036 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term1201 A u f t' s x.
Proof. exact (conj (@lem4867756 A f u s x h1) (@lem4868035 A s x P t' f u h1 h2)). Qed.
Lemma lem4868038 {A : Type'} (_60255 : A -> Prop) (_60256 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1200 A u f _60255 _60256 x.
Proof. exact (EQ_MP (@lem4868033 A u f _60255 _60256 x) (@lem4867410 A _60255 _60256 f u s x h1)). Qed.
Lemma lem4868039 {A : Type'} (_60255 : A -> Prop) (_60256 : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1200 A u f _60255 _60256 x.
Proof. exact (@lem4868038 A _60255 _60256 f u s x h1). Qed.
Lemma lem4868040 {A : Type'} (t' : type667 A) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term1122 A f u s x) : term1202 A u f t' s x.
Proof. exact (@lem4868039 A s (term578 A t' s x) f u s x h1). Qed.
Lemma lem4868043 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : False.
Proof. exact (@lem4868040 A t' f u s x h1 (@lem4868036 A s x P t' f u h1 h2)). Qed.
Lemma lem4868044 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : term871.
Proof. exact (fun h0 : ~ False => @lem4868043 A s x P t' f u h1 h2). Qed.
Lemma lem4868046 (p : Prop) : (term849 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4868047 : term871 = False.
Proof. exact (@lem4868046 False). Qed.
Lemma lem4868048 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (t' : type667 A) (f : type639 A) (u : type686 A) (h1 : term1122 A f u s x) (h2 : term558 A P t' f u) : False.
Proof. exact (EQ_MP (@lem4868047) (@lem4868044 A s x P t' f u h1 h2)). Qed.
Lemma lem4868049 {A : Type'} (P : type686 A) (t' : type667 A) (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term558 A P t' f u) (h2 : term1108 A t f u s x) : False.
Proof. exact (or_elim (@lem4866204 A t f u s x h2) (fun h0 : term1129 A f s t u x => @lem4867749 A P t' f s t u x h1 h0) (fun h0 : term1122 A f u s x => @lem4868048 A s x P t' f u h0 h1)). Qed.
Lemma lem4868050 {A : Type'} (P : type686 A) (t : A -> Prop) (f : type639 A) (u : type686 A) (s : A -> Prop) (x : A) (h1 : term307 A P f u) (h2 : term1108 A t f u s x) : False.
Proof. exact (ex_elim (@lem4865643 A P f u h1) (fun t' : type667 A => fun h0 : term560 A P f u t' => @lem4868049 A P t' t f u s x h0 h2)). Qed.
Lemma lem4868051 {A : Type'} (s : A -> Prop) (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term1111 A f u s x) (h2 : term307 A P f u) : False.
Proof. exact (ex_elim (@lem4866057 A f u s x h1) (fun t : A -> Prop => fun h0 : term1110 A f u s x t => @lem4868050 A P t f u s x h2 h0)). Qed.
Lemma lem4868052 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term983 A f u x) (h2 : term307 A P f u) : False.
Proof. exact (ex_elim (@lem4866056 A f u x h1) (fun s : A -> Prop => fun h0 : term1112 A f u x s => @lem4868051 A s x P f u h0 h2)). Qed.
Lemma lem4868053 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term983 A f u x) (h2 : term307 A P f u) : (term983 A f u x) = False.
Proof. exact (prop_ext (fun h3 : term983 A f u x => @lem4868052 A x P f u h1 h2) (fun h3 : False => @lem4865006 A f u x h1)). Qed.
Lemma lem4868054 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term983 A f u x) (h2 : term307 A P f u) : False.
Proof. exact (EQ_MP (@lem4868053 A x P f u h1 h2) (@lem4865006 A f u x h1)). Qed.
Lemma lem4868055 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term982 A f u x.
Proof. exact (fun h0 : term983 A f u x => @lem4868054 A x P f u h0 h1). Qed.
Lemma lem4868056 {A : Type'} (x : A) (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : (term953 A u f x) = (term959 A u x).
Proof. exact (EQ_MP (@lem4865005 A f u x) (@lem4868055 A x P f u h1)). Qed.
Lemma lem4868061 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term307 A P f u) : term962 A f u.
Proof. exact (fun x : A => @lem4868056 A x P f u h1). Qed.
Lemma lem4868062 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term963 A P f u.
Proof. exact (fun h0 : term307 A P f u => @lem4868061 A P f u h0). Qed.
Lemma lem4868067 {A : Type'} (f : type639 A) (u : type686 A) : term973 A f u.
Proof. exact (fun P : type686 A => @lem4868062 A P f u). Qed.
Lemma lem4868072 {A : Type'} (u : type686 A) : term977 A u.
Proof. exact (fun f : type639 A => @lem4868067 A f u). Qed.
Lemma lem4868077 {A : Type'} : term981 A.
Proof. exact (fun u : type686 A => @lem4868072 A u). Qed.
Lemma lem4868078 {A : Type'} : term980 A.
Proof. exact (EQ_MP (@lem4865000 A) (@lem4868077 A)). Qed.
Lemma lem4868079 {A : Type'} (u : type686 A) : term1203 A u.
Proof. exact (@lem4868078 A u). Qed.
Lemma lem4868080 {A : Type'} (u : type686 A) : (term1203 A u) = (term976 A u).
Proof. exact (eq_refl (term1203 A u)). Qed.
Lemma lem4868081 {A : Type'} (u : type686 A) : term976 A u.
Proof. exact (EQ_MP (@lem4868080 A u) (@lem4868079 A u)). Qed.
Lemma lem4868082 {A : Type'} (u : type686 A) (f : type639 A) : term1204 A u f.
Proof. exact (@lem4868081 A u f). Qed.
Lemma lem4868083 {A : Type'} (f : type639 A) (u : type686 A) : (term1204 A u f) = (term972 A f u).
Proof. exact (eq_refl (term1204 A u f)). Qed.
Lemma lem4868084 {A : Type'} (f : type639 A) (u : type686 A) : term972 A f u.
Proof. exact (EQ_MP (@lem4868083 A f u) (@lem4868082 A u f)). Qed.
Lemma lem4868085 {A : Type'} (f : type639 A) (u : type686 A) (P : type686 A) : term1205 A f u P.
Proof. exact (@lem4868084 A f u P). Qed.
Lemma lem4868086 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : (term1205 A f u P) = (term964 A P f u).
Proof. exact (eq_refl (term1205 A f u P)). Qed.
Lemma lem4868087 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term964 A P f u.
Proof. exact (EQ_MP (@lem4868086 A P f u) (@lem4868085 A f u P)). Qed.
Lemma lem4868089 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term964 A P f u.
Proof. exact (@lem4864620 A P f u (@lem4868087 A P f u)). Qed.
Lemma lem4868090 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term965 A P f u) : False.
Proof. exact (@lem4868089 A P f u (@lem4864604 A P f u h1)). Qed.
Lemma lem4868091 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term965 A P f u) : (term965 A P f u) = False.
Proof. exact (prop_ext (fun h2 : term965 A P f u => @lem4868090 A P f u h1) (fun h2 : False => @lem4864604 A P f u h1)). Qed.
Lemma lem4868092 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term965 A P f u) : False.
Proof. exact (EQ_MP (@lem4868091 A P f u h1) (@lem4864604 A P f u h1)). Qed.
Lemma lem4868093 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term964 A P f u.
Proof. exact (fun h0 : term965 A P f u => @lem4868092 A P f u h0). Qed.
Lemma lem4868094 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term963 A P f u.
Proof. exact (EQ_MP (@lem4864603 A P f u) (@lem4868093 A P f u)). Qed.
Lemma lem4868095 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term934 A P f u.
Proof. exact (EQ_MP (@lem4864599 A P f u) (@lem4868094 A P f u)). Qed.
Lemma lem4868096 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) : term933 A P f u.
Proof. exact (EQ_MP (@lem4864352 A P f u) (@lem4868095 A P f u)). Qed.
Lemma lem4868097 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : (term924 A u f) = (@UNIONS A u).
Proof. exact (@lem4868096 A P f u (@lem4864257 A P f u h1 h2)). Qed.
Lemma lem4868098 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : (term877 A u f) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4864246 A f u) (@lem4868097 A P f u h1 h2)). Qed.
Lemma lem4868099 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : (term252 A u f) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4864132 A f u) (@lem4868098 A P f u h1 h2)). Qed.
Lemma lem4868100 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term253 A P f u.
Proof. exact (conj (@lem4864099 A P f u h1 h2) (@lem4868099 A P f u h1 h2)). Qed.
Lemma lem4868101 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term184 A P f u.
Proof. exact (EQ_MP (@lem4861943 A P f u) (@lem4868100 A P f u h1 h2)). Qed.
Lemma lem4868102 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term185 A P f u.
Proof. exact (EQ_MP (@lem4861830 A P f u) (@lem4868101 A P f u h1 h2)). Qed.
Lemma lem4868103 {A : Type'} (P : type686 A) (f : type639 A) (u : type686 A) (h1 : term157 A u P f) (h2 : @ARBITRARY A u) : term136 A P u.
Proof. exact (ex_intro (term1206 A P u) (term182 A u f) (@lem4868102 A P f u h1 h2)). Qed.
Lemma lem4868104 {A : Type'} (f : type639 A) (P : type686 A) (u : type686 A) (h1 : @ARBITRARY A u) : term176 A f P u.
Proof. exact (fun h0 : term157 A u P f => @lem4868103 A P f u h0 h1). Qed.
Lemma lem4868109 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @ARBITRARY A u) : term179 A P u.
Proof. exact (fun f : type639 A => @lem4868104 A f P u h1). Qed.
Lemma lem4868110 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @ARBITRARY A u) : term137 A P u.
Proof. exact (EQ_MP (@lem4861575 A P u) (@lem4868109 A P u h1)). Qed.
Lemma lem4868111 {A : Type'} (P : type686 A) (u : type686 A) (h1 : @ARBITRARY A u) : term112 A P u.
Proof. exact (EQ_MP (@lem4861435 A P u) (@lem4868110 A P u h1)). Qed.
Lemma lem4868112 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : (@UNIONS A u) = s.
Proof. exact (proj2 (@lem4861391 A P u s h1)). Qed.
Lemma lem4868113 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term73 A P u s) : term69 A u P.
Proof. exact (proj1 (@lem4861391 A P u s h1)). Qed.
Lemma lem4868114 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : (@UNIONS A u) = s) : term114 A u P s.
Proof. exact (EQ_MP (@lem4861407 A P u s h2) (@lem4868111 A P u h1)). Qed.
Lemma lem4868115 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @ARBITRARY A u) (h3 : (@UNIONS A u) = s) : term59 A P s.
Proof. exact (@lem4868114 A P u s h2 h3 (@lem4861394 A u P h1)). Qed.
Lemma lem4868116 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @ARBITRARY A u) (h3 : term73 A P u s) : ((@UNIONS A u) = s) = (term59 A P s).
Proof. exact (prop_ext (fun h4 : (@UNIONS A u) = s => @lem4868115 A P u s h1 h2 h4) (fun h4 : term59 A P s => @lem4868112 A P u s h3)). Qed.
Lemma lem4868117 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term69 A u P) (h2 : @ARBITRARY A u) (h3 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4868116 A P u s h1 h2 h3) (@lem4868112 A P u s h3)). Qed.
Lemma lem4868118 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term73 A P u s) : (term69 A u P) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : term69 A u P => @lem4868117 A P u s h3 h1 h2) (fun h3 : term59 A P s => @lem4868113 A P u s h2)). Qed.
Lemma lem4868119 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4868118 A P u s h1 h2) (@lem4868113 A P u s h2)). Qed.
Lemma lem4868120 {A : Type'} (P : type686 A) (s : A -> Prop) (u : type686 A) (h1 : @ARBITRARY A u) : term1207 A u P s.
Proof. exact (fun h0 : term73 A P u s => @lem4868119 A P u s h1 h0). Qed.
Lemma lem4868121 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term73 A P u s.
Proof. exact (proj2 (@lem4861388 A P u s h1)). Qed.
Lemma lem4868122 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : @ARBITRARY A u.
Proof. exact (proj1 (@lem4861388 A P u s h1)). Qed.
Lemma lem4868123 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (@lem4868120 A P s u h1 (@lem4861389 A P u s h2)). Qed.
Lemma lem4868124 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term73 A P u s) : (@ARBITRARY A u) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : @ARBITRARY A u => @lem4868123 A P u s h1 h2) (fun h3 : term59 A P s => @lem4861390 A u h1)). Qed.
Lemma lem4868125 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term73 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4868124 A P u s h1 h2) (@lem4861390 A u h1)). Qed.
Lemma lem4868126 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term76 A P u s) : (term73 A P u s) = (term59 A P s).
Proof. exact (prop_ext (fun h3 : term73 A P u s => @lem4868125 A P u s h1 h3) (fun h3 : term59 A P s => @lem4868121 A P u s h2)). Qed.
Lemma lem4868127 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : @ARBITRARY A u) (h2 : term76 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4868126 A P u s h1 h2) (@lem4868121 A P u s h2)). Qed.
Lemma lem4868128 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : (@ARBITRARY A u) = (term59 A P s).
Proof. exact (prop_ext (fun h2 : @ARBITRARY A u => @lem4868127 A P u s h2 h1) (fun h2 : term59 A P s => @lem4868122 A P u s h1)). Qed.
Lemma lem4868129 {A : Type'} (P : type686 A) (u : type686 A) (s : A -> Prop) (h1 : term76 A P u s) : term59 A P s.
Proof. exact (EQ_MP (@lem4868128 A P u s h1) (@lem4868122 A P u s h1)). Qed.
Lemma lem4868130 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : term105 A u P s.
Proof. exact (fun h0 : term76 A P u s => @lem4868129 A P u s h0). Qed.
Lemma lem4868135 {A : Type'} (P : type686 A) (s : A -> Prop) : term108 A P s.
Proof. exact (fun u : type686 A => @lem4868130 A u P s). Qed.
Lemma lem4868137 {A : Type'} (P : type686 A) (s : A -> Prop) : term90 A P s.
Proof. exact (EQ_MP (@lem4861387 A P s) (@lem4868135 A P s)). Qed.
Lemma lem4868138 {A : Type'} (P : type686 A) (s : A -> Prop) : term1208 A P s.
Proof. exact (conj (@lem4868137 A P s) (@lem4861104 A P s)). Qed.
Lemma lem4868139 {A : Type'} (P : type686 A) (s : A -> Prop) : (term1208 A P s) = ((term82 A P s) = (@UNION_OF A (@ARBITRARY A) P s)).
Proof. exact (@lem32 (term82 A P s) (@UNION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4868140 {A : Type'} (P : type686 A) (s : A -> Prop) : (term82 A P s) = (@UNION_OF A (@ARBITRARY A) P s).
Proof. exact (EQ_MP (@lem4868139 A P s) (@lem4868138 A P s)). Qed.
Lemma lem4868145 {A : Type'} (P : type686 A) : term51 A P.
Proof. exact (fun s : A -> Prop => @lem4868140 A P s). Qed.
Lemma lem4868146 {A : Type'} (P : type686 A) : (term50 A P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (EQ_MP (@lem4861090 A P) (@lem4868145 A P)). Qed.
Lemma lem4868151 {A : Type'} : term1209 A.
Proof. exact (fun P : type686 A => @lem4868146 A P). Qed.
