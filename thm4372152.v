Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4372152_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3458960_spec.
Require Import thm3458963_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem4362895 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4362896 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4362897 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4362896 t1) (@lem4362895 t1)). Qed.
Lemma lem4362898 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4362897 t1 t2). Qed.
Lemma lem4362899 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4362900 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4362899 t1 t2) (@lem4362898 t1 t2)). Qed.
Lemma lem4362901 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4362900 t1 t2 t3). Qed.
Lemma lem4362902 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4362903 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4362902 t1 t2 t3) (@lem4362901 t1 t2 t3)). Qed.
Lemma lem4362904 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4362903 t1 t2 t3)). Qed.
Lemma lem4362905 {_103718 _103721 : Type'} (x : _103718) : term7 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4362906 {_103718 _103721 : Type'} (x : _103718) : (term7 _103718 _103721 x) = (term8 _103718 _103721 x).
Proof. exact (eq_refl (term7 _103718 _103721 x)). Qed.
Lemma lem4362907 {_103718 _103721 : Type'} (x : _103718) : term8 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4362906 _103718 _103721 x) (@lem4362905 _103718 _103721 x)). Qed.
Lemma lem4362908 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term9 _103718 _103721 x y.
Proof. exact (@lem4362907 _103718 _103721 x y). Qed.
Lemma lem4362909 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term9 _103718 _103721 x y) = (term10 _103718 _103721 x y).
Proof. exact (eq_refl (term9 _103718 _103721 x y)). Qed.
Lemma lem4362910 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term10 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4362909 _103718 _103721 x y) (@lem4362908 _103718 _103721 x y)). Qed.
Lemma lem4362911 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term11 _103718 _103721 x y s.
Proof. exact (@lem4362910 _103718 _103721 x y s). Qed.
Lemma lem4362912 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term11 _103718 _103721 x y s) = (term12 _103718 _103721 x s y).
Proof. exact (eq_refl (term11 _103718 _103721 x y s)). Qed.
Lemma lem4362913 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term12 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4362912 _103718 _103721 x s y) (@lem4362911 _103718 _103721 x y s)). Qed.
Lemma lem4362914 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term13 _103718 _103721 x s y t.
Proof. exact (@lem4362913 _103718 _103721 x s y t). Qed.
Lemma lem4362915 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term13 _103718 _103721 x s y t) = ((term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term13 _103718 _103721 x s y t)). Qed.
Lemma lem4362941 {_83095 : Type'} : term16 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4362942 {_83095 : Type'} (p : _83095 -> Prop) : term17 _83095 p.
Proof. exact (@lem4362941 _83095 p). Qed.
Lemma lem4362943 {_83095 : Type'} (p : _83095 -> Prop) : (term17 _83095 p) = (term18 _83095 p).
Proof. exact (eq_refl (term17 _83095 p)). Qed.
Lemma lem4362944 {_83095 : Type'} (p : _83095 -> Prop) : term18 _83095 p.
Proof. exact (EQ_MP (@lem4362943 _83095 p) (@lem4362942 _83095 p)). Qed.
Lemma lem4362945 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term19 _83095 p x.
Proof. exact (@lem4362944 _83095 p x). Qed.
Lemma lem4362946 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term19 _83095 p x) = ((term20 _83095 x p) = (p x)).
Proof. exact (eq_refl (term19 _83095 p x)). Qed.
Lemma lem4362955 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term21 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4362956 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = ((term22 _5106 _5107 P) = (term23 _5106 _5107 P)).
Proof. exact (eq_refl (term21 _5106 _5107 P)). Qed.
Lemma lem4362958 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4362959 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4362960 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem4362959 A s) (@lem4362958 A s)). Qed.
Lemma lem4362961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem4362960 A s t). Qed.
Lemma lem4362962 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem4362972 {_89578 _89597 _89598 : Type'} : term28 _89578 _89597 _89598.
Proof. exact (EQ_MP (@lem3458963 _89578 _89597 _89598) (@lem3458960 _89578 _89597 _89598)). Qed.
Lemma lem4362973 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) : term29 _89578 _89597 _89598 P.
Proof. exact (@lem4362972 _89578 _89597 _89598 P). Qed.
Lemma lem4362974 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) : (term29 _89578 _89597 _89598 P) = (term30 _89578 _89597 _89598 P).
Proof. exact (eq_refl (term29 _89578 _89597 _89598 P)). Qed.
Lemma lem4362975 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) : term30 _89578 _89597 _89598 P.
Proof. exact (EQ_MP (@lem4362974 _89578 _89597 _89598 P) (@lem4362973 _89578 _89597 _89598 P)). Qed.
Lemma lem4362976 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term31 _89578 _89597 _89598 P f.
Proof. exact (@lem4362975 _89578 _89597 _89598 P f). Qed.
Lemma lem4362977 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term31 _89578 _89597 _89598 P f) = ((term32 _89578 _89597 _89598 P f) = (term33 _89578 _89597 _89598 P f)).
Proof. exact (eq_refl (term31 _89578 _89597 _89598 P f)). Qed.
Lemma lem4362979 {_89520 _89534 : Type'} : term34 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem4362980 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term35 _89520 _89534 P.
Proof. exact (@lem4362979 _89520 _89534 P). Qed.
Lemma lem4362981 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term35 _89520 _89534 P) = (term36 _89520 _89534 P).
Proof. exact (eq_refl (term35 _89520 _89534 P)). Qed.
Lemma lem4362982 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term36 _89520 _89534 P.
Proof. exact (EQ_MP (@lem4362981 _89520 _89534 P) (@lem4362980 _89520 _89534 P)). Qed.
Lemma lem4362983 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term37 _89520 _89534 P f.
Proof. exact (@lem4362982 _89520 _89534 P f). Qed.
Lemma lem4362984 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term37 _89520 _89534 P f) = ((term38 _89520 _89534 P f) = (term39 _89520 _89534 P f)).
Proof. exact (eq_refl (term37 _89520 _89534 P f)). Qed.
Lemma lem4363003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4362962 A s t) (@lem4362961 A s t)). Qed.
Lemma lem4363004 {_104717 _104718 : Type'} (s : type1210 _104717 _104718) (t : type1210 _104717 _104718) : (s = t) = (term40 _104717 _104718 s t).
Proof. exact (@lem4363003 (prod _104717 _104718) s t). Qed.
Lemma lem4363005 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term41 _104717 _104718 f g) = (term42 _104717 _104718 f g)) = (term43 _104717 _104718 f g).
Proof. exact (@lem4363004 _104717 _104718 (term41 _104717 _104718 f g) (term42 _104717 _104718 f g)). Qed.
Lemma lem4363011 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4362956 _5106 _5107 P) (@lem4362955 _5106 _5107 P)). Qed.
Lemma lem4363012 {_104717 _104718 : Type'} (P : type1210 _104717 _104718) : (term44 _104717 _104718 P) = (term45 _104717 _104718 P).
Proof. exact (@lem4363011 _104718 _104717 P). Qed.
Lemma lem4363013 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term46 _104717 _104718 f g) = (term47 _104717 _104718 f g).
Proof. exact (@lem4363012 _104717 _104718 (term48 _104717 _104718 f g)). Qed.
Lemma lem4363014 {_104717 _104718 : Type'} (x : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term49 _104717 _104718 f g x) = ((term50 _104717 _104718 x f g) = (term51 _104717 _104718 x f g)).
Proof. exact (eq_refl (term49 _104717 _104718 f g x)). Qed.
Lemma lem4363015 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term52 _104717 _104718 f g) = (term48 _104717 _104718 f g).
Proof. exact (fun_ext (fun x : prod _104717 _104718 => @lem4363014 _104717 _104718 x f g)). Qed.
Lemma lem4363016 {_104717 _104718 : Type'} : (@all (prod _104717 _104718)) = (@all (prod _104717 _104718)).
Proof. exact (eq_refl (@all (prod _104717 _104718))). Qed.
Lemma lem4363017 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term46 _104717 _104718 f g) = (term43 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363016 _104717 _104718) (@lem4363015 _104717 _104718 f g)). Qed.
Lemma lem4363018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363019 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term53 _104717 _104718 f g) = (term54 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363018) (@lem4363017 _104717 _104718 f g)). Qed.
Lemma lem4363020 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) (f : type686 _104717) (g : type686 _104718) : (term55 _104717 _104718 f g p1 p2) = ((term56 _104717 _104718 p1 p2 f g) = (term57 _104717 _104718 p1 p2 f g)).
Proof. exact (eq_refl (term55 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363021 {_104717 _104718 : Type'} (p1 : _104717) (f : type686 _104717) (g : type686 _104718) : (term58 _104717 _104718 f g p1) = (term59 _104717 _104718 p1 f g).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4363020 _104717 _104718 p1 p2 f g)). Qed.
Lemma lem4363022 {_104718 : Type'} : (@all _104718) = (@all _104718).
Proof. exact (eq_refl (@all _104718)). Qed.
Lemma lem4363023 {_104717 _104718 : Type'} (p1 : _104717) (f : type686 _104717) (g : type686 _104718) : (term60 _104717 _104718 f g p1) = (term61 _104717 _104718 p1 f g).
Proof. exact (MK_COMB (@lem4363022 _104718) (@lem4363021 _104717 _104718 p1 f g)). Qed.
Lemma lem4363024 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term62 _104717 _104718 f g) = (term63 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4363023 _104717 _104718 p1 f g)). Qed.
Lemma lem4363025 {_104717 : Type'} : (@all _104717) = (@all _104717).
Proof. exact (eq_refl (@all _104717)). Qed.
Lemma lem4363026 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term47 _104717 _104718 f g) = (term64 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363025 _104717) (@lem4363024 _104717 _104718 f g)). Qed.
Lemma lem4363027 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term46 _104717 _104718 f g) = (term47 _104717 _104718 f g)) = ((term43 _104717 _104718 f g) = (term64 _104717 _104718 f g)).
Proof. exact (MK_COMB (@lem4363019 _104717 _104718 f g) (@lem4363026 _104717 _104718 f g)). Qed.
Lemma lem4363028 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term43 _104717 _104718 f g) = (term64 _104717 _104718 f g).
Proof. exact (EQ_MP (@lem4363027 _104717 _104718 f g) (@lem4363013 _104717 _104718 f g)). Qed.
Lemma lem4363035 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term41 _104717 _104718 f g) = (term42 _104717 _104718 f g)) = (term64 _104717 _104718 f g).
Proof. exact (TRANS (@lem4363005 _104717 _104718 f g) (@lem4363028 _104717 _104718 f g)). Qed.
Lemma lem4363047 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363048 {_104717 _104718 : Type'} (x : _104717) (s : _104717 -> Prop) (y : _104718) (t : _104718 -> Prop) : (term14 _104717 _104718 x y s t) = (term15 _104717 _104718 x s y t).
Proof. exact (@lem4363047 _104717 _104718 x s y t). Qed.
Lemma lem4363049 {_104717 _104718 : Type'} (p1 : _104717) (f : type686 _104717) (p2 : _104718) (g : type686 _104718) : (term56 _104717 _104718 p1 p2 f g) = (term65 _104717 _104718 p1 f p2 g).
Proof. exact (@lem4363048 _104717 _104718 p1 (@UNIONS _104717 f) p2 (@UNIONS _104718 g)). Qed.
Lemma lem4363052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363053 {_104717 _104718 : Type'} (p1 : _104717) (f : type686 _104717) (p2 : _104718) (g : type686 _104718) : (term66 _104717 _104718 p1 p2 f g) = (term67 _104717 _104718 p1 f p2 g).
Proof. exact (MK_COMB (@lem4363052) (@lem4363049 _104717 _104718 p1 f p2 g)). Qed.
Lemma lem4363055 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term32 _89578 _89597 _89598 P f) = (term33 _89578 _89597 _89598 P f).
Proof. exact (EQ_MP (@lem4362977 _89578 _89597 _89598 P f) (@lem4362976 _89578 _89597 _89598 P f)). Qed.
Lemma lem4363056 {_104717 _104718 : Type'} (P : type658 _104717 _104718) (f : type654 _104717 _104718) : (term68 _104717 _104718 P f) = (term69 _104717 _104718 P f).
Proof. exact (@lem4363055 (prod _104717 _104718) (_104718 -> Prop) (_104717 -> Prop) P f). Qed.
Lemma lem4363057 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term70 _104717 _104718 f g) = (term71 _104717 _104718 f g).
Proof. exact (@lem4363056 _104717 _104718 (term72 _104717 _104718 f g) (@CROSS _104718 _104717)). Qed.
Lemma lem4363058 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) : (term73 _104717 _104718 f g s) = (term74 _104717 _104718 s f g).
Proof. exact (eq_refl (term73 _104717 _104718 f g s)). Qed.
Lemma lem4363059 {_104718 : Type'} (t : _104718 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4363060 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (t : _104718 -> Prop) : (term75 _104717 _104718 f g s t) = (term76 _104717 _104718 s f g t).
Proof. exact (MK_COMB (@lem4363058 _104717 _104718 s f g) (@lem4363059 _104718 t)). Qed.
Lemma lem4363061 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term76 _104717 _104718 s f g t) = (term77 _104717 _104718 s f t g).
Proof. exact (eq_refl (term76 _104717 _104718 s f g t)). Qed.
Lemma lem4363062 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term75 _104717 _104718 f g s t) = (term77 _104717 _104718 s f t g).
Proof. exact (TRANS (@lem4363060 _104717 _104718 s f g t) (@lem4363061 _104717 _104718 s f t g)). Qed.
Lemma lem4363063 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) : (@SETSPEC ((prod _104717 _104718) -> Prop) GEN_PVAR_131) = (@SETSPEC ((prod _104717 _104718) -> Prop) GEN_PVAR_131).
Proof. exact (eq_refl (@SETSPEC ((prod _104717 _104718) -> Prop) GEN_PVAR_131)). Qed.
Lemma lem4363064 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term78 _104717 _104718 GEN_PVAR_131 f g s t) = (term79 _104717 _104718 GEN_PVAR_131 s f t g).
Proof. exact (MK_COMB (@lem4363063 _104717 _104718 GEN_PVAR_131) (@lem4363062 _104717 _104718 s f t g)). Qed.
Lemma lem4363065 {_104717 _104718 : Type'} (s : _104717 -> Prop) (t : _104718 -> Prop) : (@CROSS _104718 _104717 s t) = (@CROSS _104718 _104717 s t).
Proof. exact (eq_refl (@CROSS _104718 _104717 s t)). Qed.
Lemma lem4363066 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (t : _104718 -> Prop) : (term80 _104717 _104718 GEN_PVAR_131 f g s t) = (term81 _104717 _104718 GEN_PVAR_131 f g s t).
Proof. exact (MK_COMB (@lem4363064 _104717 _104718 GEN_PVAR_131 s f t g) (@lem4363065 _104717 _104718 s t)). Qed.
Lemma lem4363067 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) : (term82 _104717 _104718 GEN_PVAR_131 f g s) = (term83 _104717 _104718 GEN_PVAR_131 f g s).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4363066 _104717 _104718 GEN_PVAR_131 f g s t)). Qed.
Lemma lem4363068 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4363069 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) : (term84 _104717 _104718 GEN_PVAR_131 f g s) = (term85 _104717 _104718 GEN_PVAR_131 f g s).
Proof. exact (MK_COMB (@lem4363068 _104718) (@lem4363067 _104717 _104718 GEN_PVAR_131 f g s)). Qed.
Lemma lem4363070 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term86 _104717 _104718 GEN_PVAR_131 f g) = (term87 _104717 _104718 GEN_PVAR_131 f g).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4363069 _104717 _104718 GEN_PVAR_131 f g s)). Qed.
Lemma lem4363071 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4363072 {_104717 _104718 : Type'} (GEN_PVAR_131 : type1210 _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term88 _104717 _104718 GEN_PVAR_131 f g) = (term89 _104717 _104718 GEN_PVAR_131 f g).
Proof. exact (MK_COMB (@lem4363071 _104717) (@lem4363070 _104717 _104718 GEN_PVAR_131 f g)). Qed.
Lemma lem4363073 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term90 _104717 _104718 f g) = (term91 _104717 _104718 f g).
Proof. exact (fun_ext (fun GEN_PVAR_131 : type1210 _104717 _104718 => @lem4363072 _104717 _104718 GEN_PVAR_131 f g)). Qed.
Lemma lem4363074 {_104717 _104718 : Type'} : (@GSPEC ((prod _104717 _104718) -> Prop)) = (@GSPEC ((prod _104717 _104718) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104717 _104718) -> Prop))). Qed.
Lemma lem4363075 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term92 _104717 _104718 f g) = (term93 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363074 _104717 _104718) (@lem4363073 _104717 _104718 f g)). Qed.
Lemma lem4363076 {_104717 _104718 : Type'} : (@UNIONS (prod _104717 _104718)) = (@UNIONS (prod _104717 _104718)).
Proof. exact (eq_refl (@UNIONS (prod _104717 _104718))). Qed.
Lemma lem4363077 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term70 _104717 _104718 f g) = (term42 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363076 _104717 _104718) (@lem4363075 _104717 _104718 f g)). Qed.
Lemma lem4363078 {_104717 _104718 : Type'} : (@eq ((prod _104717 _104718) -> Prop)) = (@eq ((prod _104717 _104718) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104717 _104718) -> Prop))). Qed.
Lemma lem4363079 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term94 _104717 _104718 f g) = (term95 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363078 _104717 _104718) (@lem4363077 _104717 _104718 f g)). Qed.
Lemma lem4363080 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) : (term73 _104717 _104718 f g s) = (term74 _104717 _104718 s f g).
Proof. exact (eq_refl (term73 _104717 _104718 f g s)). Qed.
Lemma lem4363081 {_104718 : Type'} (t : _104718 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4363082 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (t : _104718 -> Prop) : (term75 _104717 _104718 f g s t) = (term76 _104717 _104718 s f g t).
Proof. exact (MK_COMB (@lem4363080 _104717 _104718 s f g) (@lem4363081 _104718 t)). Qed.
Lemma lem4363083 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term76 _104717 _104718 s f g t) = (term77 _104717 _104718 s f t g).
Proof. exact (eq_refl (term76 _104717 _104718 s f g t)). Qed.
Lemma lem4363084 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term75 _104717 _104718 f g s t) = (term77 _104717 _104718 s f t g).
Proof. exact (TRANS (@lem4363082 _104717 _104718 s f g t) (@lem4363083 _104717 _104718 s f t g)). Qed.
Lemma lem4363085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363086 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term96 _104717 _104718 f g s t) = (term97 _104717 _104718 s f t g).
Proof. exact (MK_COMB (@lem4363085) (@lem4363084 _104717 _104718 s f t g)). Qed.
Lemma lem4363087 {_104717 _104718 : Type'} (a : prod _104717 _104718) (s : _104717 -> Prop) (t : _104718 -> Prop) : (term98 _104717 _104718 a s t) = (term98 _104717 _104718 a s t).
Proof. exact (eq_refl (term98 _104717 _104718 a s t)). Qed.
Lemma lem4363088 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) (s : _104717 -> Prop) (t : _104718 -> Prop) : (term99 _104717 _104718 f g a s t) = (term100 _104717 _104718 f g a s t).
Proof. exact (MK_COMB (@lem4363086 _104717 _104718 s f t g) (@lem4363087 _104717 _104718 a s t)). Qed.
Lemma lem4363089 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) (s : _104717 -> Prop) : (term101 _104717 _104718 f g a s) = (term102 _104717 _104718 f g a s).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4363088 _104717 _104718 f g a s t)). Qed.
Lemma lem4363090 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4363091 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) (s : _104717 -> Prop) : (term103 _104717 _104718 f g a s) = (term104 _104717 _104718 f g a s).
Proof. exact (MK_COMB (@lem4363090 _104718) (@lem4363089 _104717 _104718 f g a s)). Qed.
Lemma lem4363092 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term105 _104717 _104718 f g a) = (term106 _104717 _104718 f g a).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4363091 _104717 _104718 f g a s)). Qed.
Lemma lem4363093 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4363094 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term107 _104717 _104718 f g a) = (term108 _104717 _104718 f g a).
Proof. exact (MK_COMB (@lem4363093 _104717) (@lem4363092 _104717 _104718 f g a)). Qed.
Lemma lem4363095 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) : (@SETSPEC (prod _104717 _104718) GEN_PVAR_52) = (@SETSPEC (prod _104717 _104718) GEN_PVAR_52).
Proof. exact (eq_refl (@SETSPEC (prod _104717 _104718) GEN_PVAR_52)). Qed.
Lemma lem4363096 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term109 _104717 _104718 GEN_PVAR_52 f g a) = (term110 _104717 _104718 GEN_PVAR_52 f g a).
Proof. exact (MK_COMB (@lem4363095 _104717 _104718 GEN_PVAR_52) (@lem4363094 _104717 _104718 f g a)). Qed.
Lemma lem4363097 {_104717 _104718 : Type'} (a : prod _104717 _104718) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363098 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term111 _104717 _104718 GEN_PVAR_52 f g a) = (term112 _104717 _104718 GEN_PVAR_52 f g a).
Proof. exact (MK_COMB (@lem4363096 _104717 _104718 GEN_PVAR_52 f g a) (@lem4363097 _104717 _104718 a)). Qed.
Lemma lem4363099 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term113 _104717 _104718 GEN_PVAR_52 f g) = (term114 _104717 _104718 GEN_PVAR_52 f g).
Proof. exact (fun_ext (fun a : prod _104717 _104718 => @lem4363098 _104717 _104718 GEN_PVAR_52 f g a)). Qed.
Lemma lem4363100 {_104717 _104718 : Type'} : (@ex (prod _104717 _104718)) = (@ex (prod _104717 _104718)).
Proof. exact (eq_refl (@ex (prod _104717 _104718))). Qed.
Lemma lem4363101 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term115 _104717 _104718 GEN_PVAR_52 f g) = (term116 _104717 _104718 GEN_PVAR_52 f g).
Proof. exact (MK_COMB (@lem4363100 _104717 _104718) (@lem4363099 _104717 _104718 GEN_PVAR_52 f g)). Qed.
Lemma lem4363102 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term117 _104717 _104718 f g) = (term118 _104717 _104718 f g).
Proof. exact (fun_ext (fun GEN_PVAR_52 : prod _104717 _104718 => @lem4363101 _104717 _104718 GEN_PVAR_52 f g)). Qed.
Lemma lem4363103 {_104717 _104718 : Type'} : (@GSPEC (prod _104717 _104718)) = (@GSPEC (prod _104717 _104718)).
Proof. exact (eq_refl (@GSPEC (prod _104717 _104718))). Qed.
Lemma lem4363104 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term71 _104717 _104718 f g) = (term119 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363103 _104717 _104718) (@lem4363102 _104717 _104718 f g)). Qed.
Lemma lem4363105 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term70 _104717 _104718 f g) = (term71 _104717 _104718 f g)) = ((term42 _104717 _104718 f g) = (term119 _104717 _104718 f g)).
Proof. exact (MK_COMB (@lem4363079 _104717 _104718 f g) (@lem4363104 _104717 _104718 f g)). Qed.
Lemma lem4363106 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term42 _104717 _104718 f g) = (term119 _104717 _104718 f g).
Proof. exact (EQ_MP (@lem4363105 _104717 _104718 f g) (@lem4363057 _104717 _104718 f g)). Qed.
Lemma lem4363123 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) : (term120 _104717 _104718 p1 p2) = (term120 _104717 _104718 p1 p2).
Proof. exact (eq_refl (term120 _104717 _104718 p1 p2)). Qed.
Lemma lem4363124 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) (f : type686 _104717) (g : type686 _104718) : (term57 _104717 _104718 p1 p2 f g) = (term121 _104717 _104718 p1 p2 f g).
Proof. exact (MK_COMB (@lem4363123 _104717 _104718 p1 p2) (@lem4363106 _104717 _104718 f g)). Qed.
Lemma lem4363126 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4362946 _83095 p x) (@lem4362945 _83095 p x)). Qed.
Lemma lem4363127 {_104717 _104718 : Type'} (p : type1210 _104717 _104718) (x : prod _104717 _104718) : (term122 _104717 _104718 x p) = (p x).
Proof. exact (@lem4363126 (prod _104717 _104718) p x). Qed.
Lemma lem4363128 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term123 _104717 _104718 p1 p2 f g) = (term124 _104717 _104718 f g p1 p2).
Proof. exact (@lem4363127 _104717 _104718 (term125 _104717 _104718 f g) (@pair _104717 _104718 p1 p2)). Qed.
Lemma lem4363129 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term126 _104717 _104718 f g a) = (term108 _104717 _104718 f g a).
Proof. exact (eq_refl (term126 _104717 _104718 f g a)). Qed.
Lemma lem4363130 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) : (@SETSPEC (prod _104717 _104718) GEN_PVAR_52) = (@SETSPEC (prod _104717 _104718) GEN_PVAR_52).
Proof. exact (eq_refl (@SETSPEC (prod _104717 _104718) GEN_PVAR_52)). Qed.
Lemma lem4363131 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term127 _104717 _104718 GEN_PVAR_52 f g a) = (term110 _104717 _104718 GEN_PVAR_52 f g a).
Proof. exact (MK_COMB (@lem4363130 _104717 _104718 GEN_PVAR_52) (@lem4363129 _104717 _104718 f g a)). Qed.
Lemma lem4363132 {_104717 _104718 : Type'} (a : prod _104717 _104718) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363133 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) (a : prod _104717 _104718) : (term128 _104717 _104718 GEN_PVAR_52 f g a) = (term112 _104717 _104718 GEN_PVAR_52 f g a).
Proof. exact (MK_COMB (@lem4363131 _104717 _104718 GEN_PVAR_52 f g a) (@lem4363132 _104717 _104718 a)). Qed.
Lemma lem4363134 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term129 _104717 _104718 GEN_PVAR_52 f g) = (term114 _104717 _104718 GEN_PVAR_52 f g).
Proof. exact (fun_ext (fun a : prod _104717 _104718 => @lem4363133 _104717 _104718 GEN_PVAR_52 f g a)). Qed.
Lemma lem4363135 {_104717 _104718 : Type'} : (@ex (prod _104717 _104718)) = (@ex (prod _104717 _104718)).
Proof. exact (eq_refl (@ex (prod _104717 _104718))). Qed.
Lemma lem4363136 {_104717 _104718 : Type'} (GEN_PVAR_52 : prod _104717 _104718) (f : type686 _104717) (g : type686 _104718) : (term130 _104717 _104718 GEN_PVAR_52 f g) = (term116 _104717 _104718 GEN_PVAR_52 f g).
Proof. exact (MK_COMB (@lem4363135 _104717 _104718) (@lem4363134 _104717 _104718 GEN_PVAR_52 f g)). Qed.
Lemma lem4363137 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term131 _104717 _104718 f g) = (term118 _104717 _104718 f g).
Proof. exact (fun_ext (fun GEN_PVAR_52 : prod _104717 _104718 => @lem4363136 _104717 _104718 GEN_PVAR_52 f g)). Qed.
Lemma lem4363138 {_104717 _104718 : Type'} : (@GSPEC (prod _104717 _104718)) = (@GSPEC (prod _104717 _104718)).
Proof. exact (eq_refl (@GSPEC (prod _104717 _104718))). Qed.
Lemma lem4363139 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term132 _104717 _104718 f g) = (term119 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363138 _104717 _104718) (@lem4363137 _104717 _104718 f g)). Qed.
Lemma lem4363140 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) : (term120 _104717 _104718 p1 p2) = (term120 _104717 _104718 p1 p2).
Proof. exact (eq_refl (term120 _104717 _104718 p1 p2)). Qed.
Lemma lem4363141 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) (f : type686 _104717) (g : type686 _104718) : (term123 _104717 _104718 p1 p2 f g) = (term121 _104717 _104718 p1 p2 f g).
Proof. exact (MK_COMB (@lem4363140 _104717 _104718 p1 p2) (@lem4363139 _104717 _104718 f g)). Qed.
Lemma lem4363142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363143 {_104717 _104718 : Type'} (p1 : _104717) (p2 : _104718) (f : type686 _104717) (g : type686 _104718) : (term133 _104717 _104718 p1 p2 f g) = (term134 _104717 _104718 p1 p2 f g).
Proof. exact (MK_COMB (@lem4363142) (@lem4363141 _104717 _104718 p1 p2 f g)). Qed.
Lemma lem4363144 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term124 _104717 _104718 f g p1 p2) = (term135 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term124 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363145 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term123 _104717 _104718 p1 p2 f g) = (term124 _104717 _104718 f g p1 p2)) = ((term121 _104717 _104718 p1 p2 f g) = (term135 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4363143 _104717 _104718 p1 p2 f g) (@lem4363144 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363146 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term121 _104717 _104718 p1 p2 f g) = (term135 _104717 _104718 f g p1 p2).
Proof. exact (EQ_MP (@lem4363145 _104717 _104718 f g p1 p2) (@lem4363128 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363160 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363161 {_104717 _104718 : Type'} (x : _104717) (s : _104717 -> Prop) (y : _104718) (t : _104718 -> Prop) : (term14 _104717 _104718 x y s t) = (term15 _104717 _104718 x s y t).
Proof. exact (@lem4363160 _104717 _104718 x s y t). Qed.
Lemma lem4363162 {_104717 _104718 : Type'} (p1 : _104717) (s : _104717 -> Prop) (p2 : _104718) (t : _104718 -> Prop) : (term14 _104717 _104718 p1 p2 s t) = (term15 _104717 _104718 p1 s p2 t).
Proof. exact (@lem4363161 _104717 _104718 p1 s p2 t). Qed.
Lemma lem4363165 {_104717 _104718 : Type'} (s : _104717 -> Prop) (f : type686 _104717) (t : _104718 -> Prop) (g : type686 _104718) : (term97 _104717 _104718 s f t g) = (term97 _104717 _104718 s f t g).
Proof. exact (eq_refl (term97 _104717 _104718 s f t g)). Qed.
Lemma lem4363166 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (s : _104717 -> Prop) (p2 : _104718) (t : _104718 -> Prop) : (term136 _104717 _104718 f g p1 p2 s t) = (term137 _104717 _104718 f g p1 s p2 t).
Proof. exact (MK_COMB (@lem4363165 _104717 _104718 s f t g) (@lem4363162 _104717 _104718 p1 s p2 t)). Qed.
Lemma lem4363169 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (s : _104717 -> Prop) (p2 : _104718) : (term138 _104717 _104718 f g p1 p2 s) = (term139 _104717 _104718 f g p1 s p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4363166 _104717 _104718 f g p1 s p2 t)). Qed.
Lemma lem4363170 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4363171 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (s : _104717 -> Prop) (p2 : _104718) : (term140 _104717 _104718 f g p1 p2 s) = (term141 _104717 _104718 f g p1 s p2).
Proof. exact (MK_COMB (@lem4363170 _104718) (@lem4363169 _104717 _104718 f g p1 s p2)). Qed.
Lemma lem4363176 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term142 _104717 _104718 f g p1 p2) = (term143 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4363171 _104717 _104718 f g p1 s p2)). Qed.
Lemma lem4363177 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4363178 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term135 _104717 _104718 f g p1 p2) = (term144 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4363177 _104717) (@lem4363176 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363183 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term121 _104717 _104718 p1 p2 f g) = (term144 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4363146 _104717 _104718 f g p1 p2) (@lem4363178 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363184 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term57 _104717 _104718 p1 p2 f g) = (term144 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4363124 _104717 _104718 p1 p2 f g) (@lem4363183 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363185 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term56 _104717 _104718 p1 p2 f g) = (term57 _104717 _104718 p1 p2 f g)) = ((term65 _104717 _104718 p1 f p2 g) = (term144 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4363053 _104717 _104718 p1 f p2 g) (@lem4363184 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363190 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term59 _104717 _104718 p1 f g) = (term145 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4363185 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363191 {_104718 : Type'} : (@all _104718) = (@all _104718).
Proof. exact (eq_refl (@all _104718)). Qed.
Lemma lem4363192 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term61 _104717 _104718 p1 f g) = (term146 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4363191 _104718) (@lem4363190 _104717 _104718 f g p1)). Qed.
Lemma lem4363199 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term63 _104717 _104718 f g) = (term147 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4363192 _104717 _104718 f g p1)). Qed.
Lemma lem4363200 {_104717 : Type'} : (@all _104717) = (@all _104717).
Proof. exact (eq_refl (@all _104717)). Qed.
Lemma lem4363201 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term64 _104717 _104718 f g) = (term148 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363200 _104717) (@lem4363199 _104717 _104718 f g)). Qed.
Lemma lem4363208 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term41 _104717 _104718 f g) = (term42 _104717 _104718 f g)) = (term148 _104717 _104718 f g).
Proof. exact (TRANS (@lem4363035 _104717 _104718 f g) (@lem4363201 _104717 _104718 f g)). Qed.
Lemma lem4363209 {_104717 _104718 : Type'} (f : type686 _104717) : (term149 _104717 _104718 f) = (term150 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4363208 _104717 _104718 f g)). Qed.
Lemma lem4363210 {_104718 : Type'} : (@all ((_104718 -> Prop) -> Prop)) = (@all ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4363211 {_104717 _104718 : Type'} (f : type686 _104717) : (term151 _104717 _104718 f) = (term152 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4363210 _104718) (@lem4363209 _104717 _104718 f)). Qed.
Lemma lem4363218 {_104717 _104718 : Type'} : (term153 _104717 _104718) = (term154 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4363211 _104717 _104718 f)). Qed.
Lemma lem4363219 {_104717 : Type'} : (@all ((_104717 -> Prop) -> Prop)) = (@all ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4363220 {_104717 _104718 : Type'} : (term155 _104717 _104718) = (term156 _104717 _104718).
Proof. exact (MK_COMB (@lem4363219 _104717) (@lem4363218 _104717 _104718)). Qed.
Lemma lem4363227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363228 {_104717 _104718 : Type'} : (term157 _104717 _104718) = (term158 _104717 _104718).
Proof. exact (MK_COMB (@lem4363227) (@lem4363220 _104717 _104718)). Qed.
Lemma lem4363246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4362962 A s t) (@lem4362961 A s t)). Qed.
Lemma lem4363247 {_104757 _104758 : Type'} (s : type1210 _104757 _104758) (t : type1210 _104757 _104758) : (s = t) = (term40 _104757 _104758 s t).
Proof. exact (@lem4363246 (prod _104757 _104758) s t). Qed.
Lemma lem4363248 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term159 _104757 _104758 s f) = (term160 _104757 _104758 f s)) = (term161 _104757 _104758 f s).
Proof. exact (@lem4363247 _104757 _104758 (term159 _104757 _104758 s f) (term160 _104757 _104758 f s)). Qed.
Lemma lem4363254 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4362956 _5106 _5107 P) (@lem4362955 _5106 _5107 P)). Qed.
Lemma lem4363255 {_104757 _104758 : Type'} (P : type1210 _104757 _104758) : (term44 _104757 _104758 P) = (term45 _104757 _104758 P).
Proof. exact (@lem4363254 _104758 _104757 P). Qed.
Lemma lem4363256 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term162 _104757 _104758 f s) = (term163 _104757 _104758 f s).
Proof. exact (@lem4363255 _104757 _104758 (term164 _104757 _104758 f s)). Qed.
Lemma lem4363257 {_104757 _104758 : Type'} (x : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term165 _104757 _104758 f s x) = ((term166 _104757 _104758 x s f) = (term167 _104757 _104758 x f s)).
Proof. exact (eq_refl (term165 _104757 _104758 f s x)). Qed.
Lemma lem4363258 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term168 _104757 _104758 f s) = (term164 _104757 _104758 f s).
Proof. exact (fun_ext (fun x : prod _104757 _104758 => @lem4363257 _104757 _104758 x f s)). Qed.
Lemma lem4363259 {_104757 _104758 : Type'} : (@all (prod _104757 _104758)) = (@all (prod _104757 _104758)).
Proof. exact (eq_refl (@all (prod _104757 _104758))). Qed.
Lemma lem4363260 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term162 _104757 _104758 f s) = (term161 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363259 _104757 _104758) (@lem4363258 _104757 _104758 f s)). Qed.
Lemma lem4363261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363262 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term169 _104757 _104758 f s) = (term170 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363261) (@lem4363260 _104757 _104758 f s)). Qed.
Lemma lem4363263 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term171 _104757 _104758 f s p1 p2) = ((term172 _104757 _104758 p1 p2 s f) = (term173 _104757 _104758 p1 p2 f s)).
Proof. exact (eq_refl (term171 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4363264 {_104757 _104758 : Type'} (p1 : _104757) (f : type686 _104758) (s : _104757 -> Prop) : (term174 _104757 _104758 f s p1) = (term175 _104757 _104758 p1 f s).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4363263 _104757 _104758 p1 p2 f s)). Qed.
Lemma lem4363265 {_104758 : Type'} : (@all _104758) = (@all _104758).
Proof. exact (eq_refl (@all _104758)). Qed.
Lemma lem4363266 {_104757 _104758 : Type'} (p1 : _104757) (f : type686 _104758) (s : _104757 -> Prop) : (term176 _104757 _104758 f s p1) = (term177 _104757 _104758 p1 f s).
Proof. exact (MK_COMB (@lem4363265 _104758) (@lem4363264 _104757 _104758 p1 f s)). Qed.
Lemma lem4363267 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term178 _104757 _104758 f s) = (term179 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4363266 _104757 _104758 p1 f s)). Qed.
Lemma lem4363268 {_104757 : Type'} : (@all _104757) = (@all _104757).
Proof. exact (eq_refl (@all _104757)). Qed.
Lemma lem4363269 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term163 _104757 _104758 f s) = (term180 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363268 _104757) (@lem4363267 _104757 _104758 f s)). Qed.
Lemma lem4363270 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term162 _104757 _104758 f s) = (term163 _104757 _104758 f s)) = ((term161 _104757 _104758 f s) = (term180 _104757 _104758 f s)).
Proof. exact (MK_COMB (@lem4363262 _104757 _104758 f s) (@lem4363269 _104757 _104758 f s)). Qed.
Lemma lem4363271 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term161 _104757 _104758 f s) = (term180 _104757 _104758 f s).
Proof. exact (EQ_MP (@lem4363270 _104757 _104758 f s) (@lem4363256 _104757 _104758 f s)). Qed.
Lemma lem4363278 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term159 _104757 _104758 s f) = (term160 _104757 _104758 f s)) = (term180 _104757 _104758 f s).
Proof. exact (TRANS (@lem4363248 _104757 _104758 f s) (@lem4363271 _104757 _104758 f s)). Qed.
Lemma lem4363290 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363291 {_104757 _104758 : Type'} (x : _104757) (s : _104757 -> Prop) (y : _104758) (t : _104758 -> Prop) : (term14 _104757 _104758 x y s t) = (term15 _104757 _104758 x s y t).
Proof. exact (@lem4363290 _104757 _104758 x s y t). Qed.
Lemma lem4363292 {_104757 _104758 : Type'} (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) (f : type686 _104758) : (term172 _104757 _104758 p1 p2 s f) = (term181 _104757 _104758 p1 s p2 f).
Proof. exact (@lem4363291 _104757 _104758 p1 s p2 (@UNIONS _104758 f)). Qed.
Lemma lem4363295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363296 {_104757 _104758 : Type'} (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) (f : type686 _104758) : (term182 _104757 _104758 p1 p2 s f) = (term183 _104757 _104758 p1 s p2 f).
Proof. exact (MK_COMB (@lem4363295) (@lem4363292 _104757 _104758 p1 s p2 f)). Qed.
Lemma lem4363298 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term38 _89520 _89534 P f) = (term39 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem4362984 _89520 _89534 P f) (@lem4362983 _89520 _89534 P f)). Qed.
Lemma lem4363299 {_104757 _104758 : Type'} (P : type686 _104758) (f : type857 _104757 _104758) : (term184 _104757 _104758 P f) = (term185 _104757 _104758 P f).
Proof. exact (@lem4363298 (prod _104757 _104758) (_104758 -> Prop) P f). Qed.
Lemma lem4363300 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term186 _104757 _104758 f s) = (term187 _104757 _104758 f s).
Proof. exact (@lem4363299 _104757 _104758 (term188 _104758 f) (term189 _104757 _104758 s)). Qed.
Lemma lem4363301 {_104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) : (term190 _104758 f t) = (@IN (_104758 -> Prop) t f).
Proof. exact (eq_refl (term190 _104758 f t)). Qed.
Lemma lem4363302 {_104757 _104758 : Type'} (GEN_PVAR_132 : type1210 _104757 _104758) : (@SETSPEC ((prod _104757 _104758) -> Prop) GEN_PVAR_132) = (@SETSPEC ((prod _104757 _104758) -> Prop) GEN_PVAR_132).
Proof. exact (eq_refl (@SETSPEC ((prod _104757 _104758) -> Prop) GEN_PVAR_132)). Qed.
Lemma lem4363303 {_104757 _104758 : Type'} (GEN_PVAR_132 : type1210 _104757 _104758) (t : _104758 -> Prop) (f : type686 _104758) : (term191 _104757 _104758 GEN_PVAR_132 f t) = (term192 _104757 _104758 GEN_PVAR_132 t f).
Proof. exact (MK_COMB (@lem4363302 _104757 _104758 GEN_PVAR_132) (@lem4363301 _104758 t f)). Qed.
Lemma lem4363304 {_104757 _104758 : Type'} (s : _104757 -> Prop) (t : _104758 -> Prop) : (term193 _104757 _104758 s t) = (@CROSS _104758 _104757 s t).
Proof. exact (eq_refl (term193 _104757 _104758 s t)). Qed.
Lemma lem4363305 {_104757 _104758 : Type'} (GEN_PVAR_132 : type1210 _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) (t : _104758 -> Prop) : (term194 _104757 _104758 GEN_PVAR_132 f s t) = (term195 _104757 _104758 GEN_PVAR_132 f s t).
Proof. exact (MK_COMB (@lem4363303 _104757 _104758 GEN_PVAR_132 t f) (@lem4363304 _104757 _104758 s t)). Qed.
Lemma lem4363306 {_104757 _104758 : Type'} (GEN_PVAR_132 : type1210 _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term196 _104757 _104758 GEN_PVAR_132 f s) = (term197 _104757 _104758 GEN_PVAR_132 f s).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4363305 _104757 _104758 GEN_PVAR_132 f s t)). Qed.
Lemma lem4363307 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4363308 {_104757 _104758 : Type'} (GEN_PVAR_132 : type1210 _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term198 _104757 _104758 GEN_PVAR_132 f s) = (term199 _104757 _104758 GEN_PVAR_132 f s).
Proof. exact (MK_COMB (@lem4363307 _104758) (@lem4363306 _104757 _104758 GEN_PVAR_132 f s)). Qed.
Lemma lem4363309 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term200 _104757 _104758 f s) = (term201 _104757 _104758 f s).
Proof. exact (fun_ext (fun GEN_PVAR_132 : type1210 _104757 _104758 => @lem4363308 _104757 _104758 GEN_PVAR_132 f s)). Qed.
Lemma lem4363310 {_104757 _104758 : Type'} : (@GSPEC ((prod _104757 _104758) -> Prop)) = (@GSPEC ((prod _104757 _104758) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104757 _104758) -> Prop))). Qed.
Lemma lem4363311 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term202 _104757 _104758 f s) = (term203 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363310 _104757 _104758) (@lem4363309 _104757 _104758 f s)). Qed.
Lemma lem4363312 {_104757 _104758 : Type'} : (@UNIONS (prod _104757 _104758)) = (@UNIONS (prod _104757 _104758)).
Proof. exact (eq_refl (@UNIONS (prod _104757 _104758))). Qed.
Lemma lem4363313 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term186 _104757 _104758 f s) = (term160 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363312 _104757 _104758) (@lem4363311 _104757 _104758 f s)). Qed.
Lemma lem4363314 {_104757 _104758 : Type'} : (@eq ((prod _104757 _104758) -> Prop)) = (@eq ((prod _104757 _104758) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104757 _104758) -> Prop))). Qed.
Lemma lem4363315 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term204 _104757 _104758 f s) = (term205 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363314 _104757 _104758) (@lem4363313 _104757 _104758 f s)). Qed.
Lemma lem4363316 {_104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) : (term190 _104758 f t) = (@IN (_104758 -> Prop) t f).
Proof. exact (eq_refl (term190 _104758 f t)). Qed.
Lemma lem4363317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363318 {_104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) : (term206 _104758 f t) = (term207 _104758 t f).
Proof. exact (MK_COMB (@lem4363317) (@lem4363316 _104758 t f)). Qed.
Lemma lem4363319 {_104757 _104758 : Type'} (s : _104757 -> Prop) (t : _104758 -> Prop) : (term193 _104757 _104758 s t) = (@CROSS _104758 _104757 s t).
Proof. exact (eq_refl (term193 _104757 _104758 s t)). Qed.
Lemma lem4363320 {_104757 _104758 : Type'} (a : prod _104757 _104758) : (@IN (prod _104757 _104758) a) = (@IN (prod _104757 _104758) a).
Proof. exact (eq_refl (@IN (prod _104757 _104758) a)). Qed.
Lemma lem4363321 {_104757 _104758 : Type'} (a : prod _104757 _104758) (s : _104757 -> Prop) (t : _104758 -> Prop) : (term208 _104757 _104758 a s t) = (term98 _104757 _104758 a s t).
Proof. exact (MK_COMB (@lem4363320 _104757 _104758 a) (@lem4363319 _104757 _104758 s t)). Qed.
Lemma lem4363322 {_104757 _104758 : Type'} (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) (t : _104758 -> Prop) : (term209 _104757 _104758 f a s t) = (term210 _104757 _104758 f a s t).
Proof. exact (MK_COMB (@lem4363318 _104758 t f) (@lem4363321 _104757 _104758 a s t)). Qed.
Lemma lem4363323 {_104757 _104758 : Type'} (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) : (term211 _104757 _104758 f a s) = (term212 _104757 _104758 f a s).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4363322 _104757 _104758 f a s t)). Qed.
Lemma lem4363324 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4363325 {_104757 _104758 : Type'} (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) : (term213 _104757 _104758 f a s) = (term214 _104757 _104758 f a s).
Proof. exact (MK_COMB (@lem4363324 _104758) (@lem4363323 _104757 _104758 f a s)). Qed.
Lemma lem4363326 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) : (@SETSPEC (prod _104757 _104758) GEN_PVAR_50) = (@SETSPEC (prod _104757 _104758) GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC (prod _104757 _104758) GEN_PVAR_50)). Qed.
Lemma lem4363327 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) : (term215 _104757 _104758 GEN_PVAR_50 f a s) = (term216 _104757 _104758 GEN_PVAR_50 f a s).
Proof. exact (MK_COMB (@lem4363326 _104757 _104758 GEN_PVAR_50) (@lem4363325 _104757 _104758 f a s)). Qed.
Lemma lem4363328 {_104757 _104758 : Type'} (a : prod _104757 _104758) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363329 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) (a : prod _104757 _104758) : (term217 _104757 _104758 GEN_PVAR_50 f s a) = (term218 _104757 _104758 GEN_PVAR_50 f s a).
Proof. exact (MK_COMB (@lem4363327 _104757 _104758 GEN_PVAR_50 f a s) (@lem4363328 _104757 _104758 a)). Qed.
Lemma lem4363330 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term219 _104757 _104758 GEN_PVAR_50 f s) = (term220 _104757 _104758 GEN_PVAR_50 f s).
Proof. exact (fun_ext (fun a : prod _104757 _104758 => @lem4363329 _104757 _104758 GEN_PVAR_50 f s a)). Qed.
Lemma lem4363331 {_104757 _104758 : Type'} : (@ex (prod _104757 _104758)) = (@ex (prod _104757 _104758)).
Proof. exact (eq_refl (@ex (prod _104757 _104758))). Qed.
Lemma lem4363332 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term221 _104757 _104758 GEN_PVAR_50 f s) = (term222 _104757 _104758 GEN_PVAR_50 f s).
Proof. exact (MK_COMB (@lem4363331 _104757 _104758) (@lem4363330 _104757 _104758 GEN_PVAR_50 f s)). Qed.
Lemma lem4363333 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term223 _104757 _104758 f s) = (term224 _104757 _104758 f s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : prod _104757 _104758 => @lem4363332 _104757 _104758 GEN_PVAR_50 f s)). Qed.
Lemma lem4363334 {_104757 _104758 : Type'} : (@GSPEC (prod _104757 _104758)) = (@GSPEC (prod _104757 _104758)).
Proof. exact (eq_refl (@GSPEC (prod _104757 _104758))). Qed.
Lemma lem4363335 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term187 _104757 _104758 f s) = (term225 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363334 _104757 _104758) (@lem4363333 _104757 _104758 f s)). Qed.
Lemma lem4363336 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term186 _104757 _104758 f s) = (term187 _104757 _104758 f s)) = ((term160 _104757 _104758 f s) = (term225 _104757 _104758 f s)).
Proof. exact (MK_COMB (@lem4363315 _104757 _104758 f s) (@lem4363335 _104757 _104758 f s)). Qed.
Lemma lem4363337 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term160 _104757 _104758 f s) = (term225 _104757 _104758 f s).
Proof. exact (EQ_MP (@lem4363336 _104757 _104758 f s) (@lem4363300 _104757 _104758 f s)). Qed.
Lemma lem4363348 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) : (term120 _104757 _104758 p1 p2) = (term120 _104757 _104758 p1 p2).
Proof. exact (eq_refl (term120 _104757 _104758 p1 p2)). Qed.
Lemma lem4363349 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term173 _104757 _104758 p1 p2 f s) = (term226 _104757 _104758 p1 p2 f s).
Proof. exact (MK_COMB (@lem4363348 _104757 _104758 p1 p2) (@lem4363337 _104757 _104758 f s)). Qed.
Lemma lem4363351 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4362946 _83095 p x) (@lem4362945 _83095 p x)). Qed.
Lemma lem4363352 {_104757 _104758 : Type'} (p : type1210 _104757 _104758) (x : prod _104757 _104758) : (term122 _104757 _104758 x p) = (p x).
Proof. exact (@lem4363351 (prod _104757 _104758) p x). Qed.
Lemma lem4363353 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term227 _104757 _104758 p1 p2 f s) = (term228 _104757 _104758 f s p1 p2).
Proof. exact (@lem4363352 _104757 _104758 (term229 _104757 _104758 f s) (@pair _104757 _104758 p1 p2)). Qed.
Lemma lem4363354 {_104757 _104758 : Type'} (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) : (term230 _104757 _104758 f s a) = (term214 _104757 _104758 f a s).
Proof. exact (eq_refl (term230 _104757 _104758 f s a)). Qed.
Lemma lem4363355 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) : (@SETSPEC (prod _104757 _104758) GEN_PVAR_50) = (@SETSPEC (prod _104757 _104758) GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC (prod _104757 _104758) GEN_PVAR_50)). Qed.
Lemma lem4363356 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (a : prod _104757 _104758) (s : _104757 -> Prop) : (term231 _104757 _104758 GEN_PVAR_50 f s a) = (term216 _104757 _104758 GEN_PVAR_50 f a s).
Proof. exact (MK_COMB (@lem4363355 _104757 _104758 GEN_PVAR_50) (@lem4363354 _104757 _104758 f a s)). Qed.
Lemma lem4363357 {_104757 _104758 : Type'} (a : prod _104757 _104758) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363358 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) (a : prod _104757 _104758) : (term232 _104757 _104758 GEN_PVAR_50 f s a) = (term218 _104757 _104758 GEN_PVAR_50 f s a).
Proof. exact (MK_COMB (@lem4363356 _104757 _104758 GEN_PVAR_50 f a s) (@lem4363357 _104757 _104758 a)). Qed.
Lemma lem4363359 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term233 _104757 _104758 GEN_PVAR_50 f s) = (term220 _104757 _104758 GEN_PVAR_50 f s).
Proof. exact (fun_ext (fun a : prod _104757 _104758 => @lem4363358 _104757 _104758 GEN_PVAR_50 f s a)). Qed.
Lemma lem4363360 {_104757 _104758 : Type'} : (@ex (prod _104757 _104758)) = (@ex (prod _104757 _104758)).
Proof. exact (eq_refl (@ex (prod _104757 _104758))). Qed.
Lemma lem4363361 {_104757 _104758 : Type'} (GEN_PVAR_50 : prod _104757 _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term234 _104757 _104758 GEN_PVAR_50 f s) = (term222 _104757 _104758 GEN_PVAR_50 f s).
Proof. exact (MK_COMB (@lem4363360 _104757 _104758) (@lem4363359 _104757 _104758 GEN_PVAR_50 f s)). Qed.
Lemma lem4363362 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term235 _104757 _104758 f s) = (term224 _104757 _104758 f s).
Proof. exact (fun_ext (fun GEN_PVAR_50 : prod _104757 _104758 => @lem4363361 _104757 _104758 GEN_PVAR_50 f s)). Qed.
Lemma lem4363363 {_104757 _104758 : Type'} : (@GSPEC (prod _104757 _104758)) = (@GSPEC (prod _104757 _104758)).
Proof. exact (eq_refl (@GSPEC (prod _104757 _104758))). Qed.
Lemma lem4363364 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term236 _104757 _104758 f s) = (term225 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363363 _104757 _104758) (@lem4363362 _104757 _104758 f s)). Qed.
Lemma lem4363365 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) : (term120 _104757 _104758 p1 p2) = (term120 _104757 _104758 p1 p2).
Proof. exact (eq_refl (term120 _104757 _104758 p1 p2)). Qed.
Lemma lem4363366 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term227 _104757 _104758 p1 p2 f s) = (term226 _104757 _104758 p1 p2 f s).
Proof. exact (MK_COMB (@lem4363365 _104757 _104758 p1 p2) (@lem4363364 _104757 _104758 f s)). Qed.
Lemma lem4363367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363368 {_104757 _104758 : Type'} (p1 : _104757) (p2 : _104758) (f : type686 _104758) (s : _104757 -> Prop) : (term237 _104757 _104758 p1 p2 f s) = (term238 _104757 _104758 p1 p2 f s).
Proof. exact (MK_COMB (@lem4363367) (@lem4363366 _104757 _104758 p1 p2 f s)). Qed.
Lemma lem4363369 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (p2 : _104758) (s : _104757 -> Prop) : (term228 _104757 _104758 f s p1 p2) = (term239 _104757 _104758 f p1 p2 s).
Proof. exact (eq_refl (term228 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4363370 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (p2 : _104758) (s : _104757 -> Prop) : ((term227 _104757 _104758 p1 p2 f s) = (term228 _104757 _104758 f s p1 p2)) = ((term226 _104757 _104758 p1 p2 f s) = (term239 _104757 _104758 f p1 p2 s)).
Proof. exact (MK_COMB (@lem4363368 _104757 _104758 p1 p2 f s) (@lem4363369 _104757 _104758 f p1 p2 s)). Qed.
Lemma lem4363371 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (p2 : _104758) (s : _104757 -> Prop) : (term226 _104757 _104758 p1 p2 f s) = (term239 _104757 _104758 f p1 p2 s).
Proof. exact (EQ_MP (@lem4363370 _104757 _104758 f p1 p2 s) (@lem4363353 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4363379 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363380 {_104757 _104758 : Type'} (x : _104757) (s : _104757 -> Prop) (y : _104758) (t : _104758 -> Prop) : (term14 _104757 _104758 x y s t) = (term15 _104757 _104758 x s y t).
Proof. exact (@lem4363379 _104757 _104758 x s y t). Qed.
Lemma lem4363381 {_104757 _104758 : Type'} (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) (t : _104758 -> Prop) : (term14 _104757 _104758 p1 p2 s t) = (term15 _104757 _104758 p1 s p2 t).
Proof. exact (@lem4363380 _104757 _104758 p1 s p2 t). Qed.
Lemma lem4363384 {_104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) : (term207 _104758 t f) = (term207 _104758 t f).
Proof. exact (eq_refl (term207 _104758 t f)). Qed.
Lemma lem4363385 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) (t : _104758 -> Prop) : (term240 _104757 _104758 f p1 p2 s t) = (term241 _104757 _104758 f p1 s p2 t).
Proof. exact (MK_COMB (@lem4363384 _104758 t f) (@lem4363381 _104757 _104758 p1 s p2 t)). Qed.
Lemma lem4363388 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) : (term242 _104757 _104758 f p1 p2 s) = (term243 _104757 _104758 f p1 s p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4363385 _104757 _104758 f p1 s p2 t)). Qed.
Lemma lem4363389 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4363390 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) : (term239 _104757 _104758 f p1 p2 s) = (term244 _104757 _104758 f p1 s p2).
Proof. exact (MK_COMB (@lem4363389 _104758) (@lem4363388 _104757 _104758 f p1 s p2)). Qed.
Lemma lem4363395 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) : (term226 _104757 _104758 p1 p2 f s) = (term244 _104757 _104758 f p1 s p2).
Proof. exact (TRANS (@lem4363371 _104757 _104758 f p1 p2 s) (@lem4363390 _104757 _104758 f p1 s p2)). Qed.
Lemma lem4363396 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) : (term173 _104757 _104758 p1 p2 f s) = (term244 _104757 _104758 f p1 s p2).
Proof. exact (TRANS (@lem4363349 _104757 _104758 p1 p2 f s) (@lem4363395 _104757 _104758 f p1 s p2)). Qed.
Lemma lem4363397 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) (p2 : _104758) : ((term172 _104757 _104758 p1 p2 s f) = (term173 _104757 _104758 p1 p2 f s)) = ((term181 _104757 _104758 p1 s p2 f) = (term244 _104757 _104758 f p1 s p2)).
Proof. exact (MK_COMB (@lem4363296 _104757 _104758 p1 s p2 f) (@lem4363396 _104757 _104758 f p1 s p2)). Qed.
Lemma lem4363402 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) : (term175 _104757 _104758 p1 f s) = (term245 _104757 _104758 f p1 s).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4363397 _104757 _104758 f p1 s p2)). Qed.
Lemma lem4363403 {_104758 : Type'} : (@all _104758) = (@all _104758).
Proof. exact (eq_refl (@all _104758)). Qed.
Lemma lem4363404 {_104757 _104758 : Type'} (f : type686 _104758) (p1 : _104757) (s : _104757 -> Prop) : (term177 _104757 _104758 p1 f s) = (term246 _104757 _104758 f p1 s).
Proof. exact (MK_COMB (@lem4363403 _104758) (@lem4363402 _104757 _104758 f p1 s)). Qed.
Lemma lem4363411 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term179 _104757 _104758 f s) = (term247 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4363404 _104757 _104758 f p1 s)). Qed.
Lemma lem4363412 {_104757 : Type'} : (@all _104757) = (@all _104757).
Proof. exact (eq_refl (@all _104757)). Qed.
Lemma lem4363413 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term180 _104757 _104758 f s) = (term248 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4363412 _104757) (@lem4363411 _104757 _104758 f s)). Qed.
Lemma lem4363420 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term159 _104757 _104758 s f) = (term160 _104757 _104758 f s)) = (term248 _104757 _104758 f s).
Proof. exact (TRANS (@lem4363278 _104757 _104758 f s) (@lem4363413 _104757 _104758 f s)). Qed.
Lemma lem4363421 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term249 _104757 _104758 s) = (term250 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4363420 _104757 _104758 f s)). Qed.
Lemma lem4363422 {_104758 : Type'} : (@all ((_104758 -> Prop) -> Prop)) = (@all ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4363423 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term251 _104757 _104758 s) = (term252 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4363422 _104758) (@lem4363421 _104757 _104758 s)). Qed.
Lemma lem4363430 {_104757 _104758 : Type'} : (term253 _104757 _104758) = (term254 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4363423 _104757 _104758 s)). Qed.
Lemma lem4363431 {_104757 : Type'} : (@all (_104757 -> Prop)) = (@all (_104757 -> Prop)).
Proof. exact (eq_refl (@all (_104757 -> Prop))). Qed.
Lemma lem4363432 {_104757 _104758 : Type'} : (term255 _104757 _104758) = (term256 _104757 _104758).
Proof. exact (MK_COMB (@lem4363431 _104757) (@lem4363430 _104757 _104758)). Qed.
Lemma lem4363439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363440 {_104757 _104758 : Type'} : (term257 _104757 _104758) = (term258 _104757 _104758).
Proof. exact (MK_COMB (@lem4363439) (@lem4363432 _104757 _104758)). Qed.
Lemma lem4363456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4362962 A s t) (@lem4362961 A s t)). Qed.
Lemma lem4363457 {_104795 _104796 : Type'} (s : type1210 _104795 _104796) (t : type1210 _104795 _104796) : (s = t) = (term40 _104795 _104796 s t).
Proof. exact (@lem4363456 (prod _104795 _104796) s t). Qed.
Lemma lem4363458 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term259 _104795 _104796 f t) = (term260 _104795 _104796 f t)) = (term261 _104795 _104796 f t).
Proof. exact (@lem4363457 _104795 _104796 (term259 _104795 _104796 f t) (term260 _104795 _104796 f t)). Qed.
Lemma lem4363464 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4362956 _5106 _5107 P) (@lem4362955 _5106 _5107 P)). Qed.
Lemma lem4363465 {_104795 _104796 : Type'} (P : type1210 _104795 _104796) : (term44 _104795 _104796 P) = (term45 _104795 _104796 P).
Proof. exact (@lem4363464 _104796 _104795 P). Qed.
Lemma lem4363466 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term262 _104795 _104796 f t) = (term263 _104795 _104796 f t).
Proof. exact (@lem4363465 _104795 _104796 (term264 _104795 _104796 f t)). Qed.
Lemma lem4363467 {_104795 _104796 : Type'} (x : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term265 _104795 _104796 f t x) = ((term266 _104795 _104796 x f t) = (term267 _104795 _104796 x f t)).
Proof. exact (eq_refl (term265 _104795 _104796 f t x)). Qed.
Lemma lem4363468 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term268 _104795 _104796 f t) = (term264 _104795 _104796 f t).
Proof. exact (fun_ext (fun x : prod _104795 _104796 => @lem4363467 _104795 _104796 x f t)). Qed.
Lemma lem4363469 {_104795 _104796 : Type'} : (@all (prod _104795 _104796)) = (@all (prod _104795 _104796)).
Proof. exact (eq_refl (@all (prod _104795 _104796))). Qed.
Lemma lem4363470 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term262 _104795 _104796 f t) = (term261 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363469 _104795 _104796) (@lem4363468 _104795 _104796 f t)). Qed.
Lemma lem4363471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363472 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term269 _104795 _104796 f t) = (term270 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363471) (@lem4363470 _104795 _104796 f t)). Qed.
Lemma lem4363473 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term271 _104795 _104796 f t p1 p2) = ((term272 _104795 _104796 p1 p2 f t) = (term273 _104795 _104796 p1 p2 f t)).
Proof. exact (eq_refl (term271 _104795 _104796 f t p1 p2)). Qed.
Lemma lem4363474 {_104795 _104796 : Type'} (p1 : _104795) (f : type686 _104795) (t : _104796 -> Prop) : (term274 _104795 _104796 f t p1) = (term275 _104795 _104796 p1 f t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4363473 _104795 _104796 p1 p2 f t)). Qed.
Lemma lem4363475 {_104796 : Type'} : (@all _104796) = (@all _104796).
Proof. exact (eq_refl (@all _104796)). Qed.
Lemma lem4363476 {_104795 _104796 : Type'} (p1 : _104795) (f : type686 _104795) (t : _104796 -> Prop) : (term276 _104795 _104796 f t p1) = (term277 _104795 _104796 p1 f t).
Proof. exact (MK_COMB (@lem4363475 _104796) (@lem4363474 _104795 _104796 p1 f t)). Qed.
Lemma lem4363477 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term278 _104795 _104796 f t) = (term279 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4363476 _104795 _104796 p1 f t)). Qed.
Lemma lem4363478 {_104795 : Type'} : (@all _104795) = (@all _104795).
Proof. exact (eq_refl (@all _104795)). Qed.
Lemma lem4363479 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term263 _104795 _104796 f t) = (term280 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363478 _104795) (@lem4363477 _104795 _104796 f t)). Qed.
Lemma lem4363480 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term262 _104795 _104796 f t) = (term263 _104795 _104796 f t)) = ((term261 _104795 _104796 f t) = (term280 _104795 _104796 f t)).
Proof. exact (MK_COMB (@lem4363472 _104795 _104796 f t) (@lem4363479 _104795 _104796 f t)). Qed.
Lemma lem4363481 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term261 _104795 _104796 f t) = (term280 _104795 _104796 f t).
Proof. exact (EQ_MP (@lem4363480 _104795 _104796 f t) (@lem4363466 _104795 _104796 f t)). Qed.
Lemma lem4363488 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term259 _104795 _104796 f t) = (term260 _104795 _104796 f t)) = (term280 _104795 _104796 f t).
Proof. exact (TRANS (@lem4363458 _104795 _104796 f t) (@lem4363481 _104795 _104796 f t)). Qed.
Lemma lem4363500 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363501 {_104795 _104796 : Type'} (x : _104795) (s : _104795 -> Prop) (y : _104796) (t : _104796 -> Prop) : (term14 _104795 _104796 x y s t) = (term15 _104795 _104796 x s y t).
Proof. exact (@lem4363500 _104795 _104796 x s y t). Qed.
Lemma lem4363502 {_104795 _104796 : Type'} (p1 : _104795) (f : type686 _104795) (p2 : _104796) (t : _104796 -> Prop) : (term272 _104795 _104796 p1 p2 f t) = (term281 _104795 _104796 p1 f p2 t).
Proof. exact (@lem4363501 _104795 _104796 p1 (@UNIONS _104795 f) p2 t). Qed.
Lemma lem4363505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363506 {_104795 _104796 : Type'} (p1 : _104795) (f : type686 _104795) (p2 : _104796) (t : _104796 -> Prop) : (term282 _104795 _104796 p1 p2 f t) = (term283 _104795 _104796 p1 f p2 t).
Proof. exact (MK_COMB (@lem4363505) (@lem4363502 _104795 _104796 p1 f p2 t)). Qed.
Lemma lem4363508 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term38 _89520 _89534 P f) = (term39 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem4362984 _89520 _89534 P f) (@lem4362983 _89520 _89534 P f)). Qed.
Lemma lem4363509 {_104795 _104796 : Type'} (P : type686 _104795) (f : type664 _104795 _104796) : (term284 _104795 _104796 P f) = (term285 _104795 _104796 P f).
Proof. exact (@lem4363508 (prod _104795 _104796) (_104795 -> Prop) P f). Qed.
Lemma lem4363510 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term286 _104795 _104796 f t) = (term287 _104795 _104796 f t).
Proof. exact (@lem4363509 _104795 _104796 (term188 _104795 f) (term288 _104795 _104796 t)). Qed.
Lemma lem4363511 {_104795 : Type'} (s : _104795 -> Prop) (f : type686 _104795) : (term190 _104795 f s) = (@IN (_104795 -> Prop) s f).
Proof. exact (eq_refl (term190 _104795 f s)). Qed.
Lemma lem4363512 {_104795 _104796 : Type'} (GEN_PVAR_133 : type1210 _104795 _104796) : (@SETSPEC ((prod _104795 _104796) -> Prop) GEN_PVAR_133) = (@SETSPEC ((prod _104795 _104796) -> Prop) GEN_PVAR_133).
Proof. exact (eq_refl (@SETSPEC ((prod _104795 _104796) -> Prop) GEN_PVAR_133)). Qed.
Lemma lem4363513 {_104795 _104796 : Type'} (GEN_PVAR_133 : type1210 _104795 _104796) (s : _104795 -> Prop) (f : type686 _104795) : (term289 _104795 _104796 GEN_PVAR_133 f s) = (term290 _104795 _104796 GEN_PVAR_133 s f).
Proof. exact (MK_COMB (@lem4363512 _104795 _104796 GEN_PVAR_133) (@lem4363511 _104795 s f)). Qed.
Lemma lem4363514 {_104795 _104796 : Type'} (s : _104795 -> Prop) (t : _104796 -> Prop) : (term291 _104795 _104796 t s) = (@CROSS _104796 _104795 s t).
Proof. exact (eq_refl (term291 _104795 _104796 t s)). Qed.
Lemma lem4363515 {_104795 _104796 : Type'} (GEN_PVAR_133 : type1210 _104795 _104796) (f : type686 _104795) (s : _104795 -> Prop) (t : _104796 -> Prop) : (term292 _104795 _104796 GEN_PVAR_133 f t s) = (term293 _104795 _104796 GEN_PVAR_133 f s t).
Proof. exact (MK_COMB (@lem4363513 _104795 _104796 GEN_PVAR_133 s f) (@lem4363514 _104795 _104796 s t)). Qed.
Lemma lem4363516 {_104795 _104796 : Type'} (GEN_PVAR_133 : type1210 _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term294 _104795 _104796 GEN_PVAR_133 f t) = (term295 _104795 _104796 GEN_PVAR_133 f t).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4363515 _104795 _104796 GEN_PVAR_133 f s t)). Qed.
Lemma lem4363517 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4363518 {_104795 _104796 : Type'} (GEN_PVAR_133 : type1210 _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term296 _104795 _104796 GEN_PVAR_133 f t) = (term297 _104795 _104796 GEN_PVAR_133 f t).
Proof. exact (MK_COMB (@lem4363517 _104795) (@lem4363516 _104795 _104796 GEN_PVAR_133 f t)). Qed.
Lemma lem4363519 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term298 _104795 _104796 f t) = (term299 _104795 _104796 f t).
Proof. exact (fun_ext (fun GEN_PVAR_133 : type1210 _104795 _104796 => @lem4363518 _104795 _104796 GEN_PVAR_133 f t)). Qed.
Lemma lem4363520 {_104795 _104796 : Type'} : (@GSPEC ((prod _104795 _104796) -> Prop)) = (@GSPEC ((prod _104795 _104796) -> Prop)).
Proof. exact (eq_refl (@GSPEC ((prod _104795 _104796) -> Prop))). Qed.
Lemma lem4363521 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term300 _104795 _104796 f t) = (term301 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363520 _104795 _104796) (@lem4363519 _104795 _104796 f t)). Qed.
Lemma lem4363522 {_104795 _104796 : Type'} : (@UNIONS (prod _104795 _104796)) = (@UNIONS (prod _104795 _104796)).
Proof. exact (eq_refl (@UNIONS (prod _104795 _104796))). Qed.
Lemma lem4363523 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term286 _104795 _104796 f t) = (term260 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363522 _104795 _104796) (@lem4363521 _104795 _104796 f t)). Qed.
Lemma lem4363524 {_104795 _104796 : Type'} : (@eq ((prod _104795 _104796) -> Prop)) = (@eq ((prod _104795 _104796) -> Prop)).
Proof. exact (eq_refl (@eq ((prod _104795 _104796) -> Prop))). Qed.
Lemma lem4363525 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term302 _104795 _104796 f t) = (term303 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363524 _104795 _104796) (@lem4363523 _104795 _104796 f t)). Qed.
Lemma lem4363526 {_104795 : Type'} (s : _104795 -> Prop) (f : type686 _104795) : (term190 _104795 f s) = (@IN (_104795 -> Prop) s f).
Proof. exact (eq_refl (term190 _104795 f s)). Qed.
Lemma lem4363527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363528 {_104795 : Type'} (s : _104795 -> Prop) (f : type686 _104795) : (term206 _104795 f s) = (term207 _104795 s f).
Proof. exact (MK_COMB (@lem4363527) (@lem4363526 _104795 s f)). Qed.
Lemma lem4363529 {_104795 _104796 : Type'} (s : _104795 -> Prop) (t : _104796 -> Prop) : (term291 _104795 _104796 t s) = (@CROSS _104796 _104795 s t).
Proof. exact (eq_refl (term291 _104795 _104796 t s)). Qed.
Lemma lem4363530 {_104795 _104796 : Type'} (a : prod _104795 _104796) : (@IN (prod _104795 _104796) a) = (@IN (prod _104795 _104796) a).
Proof. exact (eq_refl (@IN (prod _104795 _104796) a)). Qed.
Lemma lem4363531 {_104795 _104796 : Type'} (a : prod _104795 _104796) (s : _104795 -> Prop) (t : _104796 -> Prop) : (term304 _104795 _104796 a t s) = (term98 _104795 _104796 a s t).
Proof. exact (MK_COMB (@lem4363530 _104795 _104796 a) (@lem4363529 _104795 _104796 s t)). Qed.
Lemma lem4363532 {_104795 _104796 : Type'} (f : type686 _104795) (a : prod _104795 _104796) (s : _104795 -> Prop) (t : _104796 -> Prop) : (term305 _104795 _104796 f a t s) = (term306 _104795 _104796 f a s t).
Proof. exact (MK_COMB (@lem4363528 _104795 s f) (@lem4363531 _104795 _104796 a s t)). Qed.
Lemma lem4363533 {_104795 _104796 : Type'} (f : type686 _104795) (a : prod _104795 _104796) (t : _104796 -> Prop) : (term307 _104795 _104796 f a t) = (term308 _104795 _104796 f a t).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4363532 _104795 _104796 f a s t)). Qed.
Lemma lem4363534 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4363535 {_104795 _104796 : Type'} (f : type686 _104795) (a : prod _104795 _104796) (t : _104796 -> Prop) : (term309 _104795 _104796 f a t) = (term310 _104795 _104796 f a t).
Proof. exact (MK_COMB (@lem4363534 _104795) (@lem4363533 _104795 _104796 f a t)). Qed.
Lemma lem4363536 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) : (@SETSPEC (prod _104795 _104796) GEN_PVAR_50) = (@SETSPEC (prod _104795 _104796) GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC (prod _104795 _104796) GEN_PVAR_50)). Qed.
Lemma lem4363537 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (a : prod _104795 _104796) (t : _104796 -> Prop) : (term311 _104795 _104796 GEN_PVAR_50 f a t) = (term312 _104795 _104796 GEN_PVAR_50 f a t).
Proof. exact (MK_COMB (@lem4363536 _104795 _104796 GEN_PVAR_50) (@lem4363535 _104795 _104796 f a t)). Qed.
Lemma lem4363538 {_104795 _104796 : Type'} (a : prod _104795 _104796) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363539 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) (a : prod _104795 _104796) : (term313 _104795 _104796 GEN_PVAR_50 f t a) = (term314 _104795 _104796 GEN_PVAR_50 f t a).
Proof. exact (MK_COMB (@lem4363537 _104795 _104796 GEN_PVAR_50 f a t) (@lem4363538 _104795 _104796 a)). Qed.
Lemma lem4363540 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term315 _104795 _104796 GEN_PVAR_50 f t) = (term316 _104795 _104796 GEN_PVAR_50 f t).
Proof. exact (fun_ext (fun a : prod _104795 _104796 => @lem4363539 _104795 _104796 GEN_PVAR_50 f t a)). Qed.
Lemma lem4363541 {_104795 _104796 : Type'} : (@ex (prod _104795 _104796)) = (@ex (prod _104795 _104796)).
Proof. exact (eq_refl (@ex (prod _104795 _104796))). Qed.
Lemma lem4363542 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term317 _104795 _104796 GEN_PVAR_50 f t) = (term318 _104795 _104796 GEN_PVAR_50 f t).
Proof. exact (MK_COMB (@lem4363541 _104795 _104796) (@lem4363540 _104795 _104796 GEN_PVAR_50 f t)). Qed.
Lemma lem4363543 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term319 _104795 _104796 f t) = (term320 _104795 _104796 f t).
Proof. exact (fun_ext (fun GEN_PVAR_50 : prod _104795 _104796 => @lem4363542 _104795 _104796 GEN_PVAR_50 f t)). Qed.
Lemma lem4363544 {_104795 _104796 : Type'} : (@GSPEC (prod _104795 _104796)) = (@GSPEC (prod _104795 _104796)).
Proof. exact (eq_refl (@GSPEC (prod _104795 _104796))). Qed.
Lemma lem4363545 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term287 _104795 _104796 f t) = (term321 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363544 _104795 _104796) (@lem4363543 _104795 _104796 f t)). Qed.
Lemma lem4363546 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term286 _104795 _104796 f t) = (term287 _104795 _104796 f t)) = ((term260 _104795 _104796 f t) = (term321 _104795 _104796 f t)).
Proof. exact (MK_COMB (@lem4363525 _104795 _104796 f t) (@lem4363545 _104795 _104796 f t)). Qed.
Lemma lem4363547 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term260 _104795 _104796 f t) = (term321 _104795 _104796 f t).
Proof. exact (EQ_MP (@lem4363546 _104795 _104796 f t) (@lem4363510 _104795 _104796 f t)). Qed.
Lemma lem4363558 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) : (term120 _104795 _104796 p1 p2) = (term120 _104795 _104796 p1 p2).
Proof. exact (eq_refl (term120 _104795 _104796 p1 p2)). Qed.
Lemma lem4363559 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term273 _104795 _104796 p1 p2 f t) = (term322 _104795 _104796 p1 p2 f t).
Proof. exact (MK_COMB (@lem4363558 _104795 _104796 p1 p2) (@lem4363547 _104795 _104796 f t)). Qed.
Lemma lem4363561 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term20 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4362946 _83095 p x) (@lem4362945 _83095 p x)). Qed.
Lemma lem4363562 {_104795 _104796 : Type'} (p : type1210 _104795 _104796) (x : prod _104795 _104796) : (term122 _104795 _104796 x p) = (p x).
Proof. exact (@lem4363561 (prod _104795 _104796) p x). Qed.
Lemma lem4363563 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) (p1 : _104795) (p2 : _104796) : (term323 _104795 _104796 p1 p2 f t) = (term324 _104795 _104796 f t p1 p2).
Proof. exact (@lem4363562 _104795 _104796 (term325 _104795 _104796 f t) (@pair _104795 _104796 p1 p2)). Qed.
Lemma lem4363564 {_104795 _104796 : Type'} (f : type686 _104795) (a : prod _104795 _104796) (t : _104796 -> Prop) : (term326 _104795 _104796 f t a) = (term310 _104795 _104796 f a t).
Proof. exact (eq_refl (term326 _104795 _104796 f t a)). Qed.
Lemma lem4363565 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) : (@SETSPEC (prod _104795 _104796) GEN_PVAR_50) = (@SETSPEC (prod _104795 _104796) GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC (prod _104795 _104796) GEN_PVAR_50)). Qed.
Lemma lem4363566 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (a : prod _104795 _104796) (t : _104796 -> Prop) : (term327 _104795 _104796 GEN_PVAR_50 f t a) = (term312 _104795 _104796 GEN_PVAR_50 f a t).
Proof. exact (MK_COMB (@lem4363565 _104795 _104796 GEN_PVAR_50) (@lem4363564 _104795 _104796 f a t)). Qed.
Lemma lem4363567 {_104795 _104796 : Type'} (a : prod _104795 _104796) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4363568 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) (a : prod _104795 _104796) : (term328 _104795 _104796 GEN_PVAR_50 f t a) = (term314 _104795 _104796 GEN_PVAR_50 f t a).
Proof. exact (MK_COMB (@lem4363566 _104795 _104796 GEN_PVAR_50 f a t) (@lem4363567 _104795 _104796 a)). Qed.
Lemma lem4363569 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term329 _104795 _104796 GEN_PVAR_50 f t) = (term316 _104795 _104796 GEN_PVAR_50 f t).
Proof. exact (fun_ext (fun a : prod _104795 _104796 => @lem4363568 _104795 _104796 GEN_PVAR_50 f t a)). Qed.
Lemma lem4363570 {_104795 _104796 : Type'} : (@ex (prod _104795 _104796)) = (@ex (prod _104795 _104796)).
Proof. exact (eq_refl (@ex (prod _104795 _104796))). Qed.
Lemma lem4363571 {_104795 _104796 : Type'} (GEN_PVAR_50 : prod _104795 _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term330 _104795 _104796 GEN_PVAR_50 f t) = (term318 _104795 _104796 GEN_PVAR_50 f t).
Proof. exact (MK_COMB (@lem4363570 _104795 _104796) (@lem4363569 _104795 _104796 GEN_PVAR_50 f t)). Qed.
Lemma lem4363572 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term331 _104795 _104796 f t) = (term320 _104795 _104796 f t).
Proof. exact (fun_ext (fun GEN_PVAR_50 : prod _104795 _104796 => @lem4363571 _104795 _104796 GEN_PVAR_50 f t)). Qed.
Lemma lem4363573 {_104795 _104796 : Type'} : (@GSPEC (prod _104795 _104796)) = (@GSPEC (prod _104795 _104796)).
Proof. exact (eq_refl (@GSPEC (prod _104795 _104796))). Qed.
Lemma lem4363574 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term332 _104795 _104796 f t) = (term321 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363573 _104795 _104796) (@lem4363572 _104795 _104796 f t)). Qed.
Lemma lem4363575 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) : (term120 _104795 _104796 p1 p2) = (term120 _104795 _104796 p1 p2).
Proof. exact (eq_refl (term120 _104795 _104796 p1 p2)). Qed.
Lemma lem4363576 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term323 _104795 _104796 p1 p2 f t) = (term322 _104795 _104796 p1 p2 f t).
Proof. exact (MK_COMB (@lem4363575 _104795 _104796 p1 p2) (@lem4363574 _104795 _104796 f t)). Qed.
Lemma lem4363577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363578 {_104795 _104796 : Type'} (p1 : _104795) (p2 : _104796) (f : type686 _104795) (t : _104796 -> Prop) : (term333 _104795 _104796 p1 p2 f t) = (term334 _104795 _104796 p1 p2 f t).
Proof. exact (MK_COMB (@lem4363577) (@lem4363576 _104795 _104796 p1 p2 f t)). Qed.
Lemma lem4363579 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term324 _104795 _104796 f t p1 p2) = (term335 _104795 _104796 f p1 p2 t).
Proof. exact (eq_refl (term324 _104795 _104796 f t p1 p2)). Qed.
Lemma lem4363580 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : ((term323 _104795 _104796 p1 p2 f t) = (term324 _104795 _104796 f t p1 p2)) = ((term322 _104795 _104796 p1 p2 f t) = (term335 _104795 _104796 f p1 p2 t)).
Proof. exact (MK_COMB (@lem4363578 _104795 _104796 p1 p2 f t) (@lem4363579 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363581 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term322 _104795 _104796 p1 p2 f t) = (term335 _104795 _104796 f p1 p2 t).
Proof. exact (EQ_MP (@lem4363580 _104795 _104796 f p1 p2 t) (@lem4363563 _104795 _104796 f t p1 p2)). Qed.
Lemma lem4363589 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x y s t) = (term15 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4362915 _103718 _103721 x s y t) (@lem4362914 _103718 _103721 x s y t)). Qed.
Lemma lem4363590 {_104795 _104796 : Type'} (x : _104795) (s : _104795 -> Prop) (y : _104796) (t : _104796 -> Prop) : (term14 _104795 _104796 x y s t) = (term15 _104795 _104796 x s y t).
Proof. exact (@lem4363589 _104795 _104796 x s y t). Qed.
Lemma lem4363591 {_104795 _104796 : Type'} (p1 : _104795) (s : _104795 -> Prop) (p2 : _104796) (t : _104796 -> Prop) : (term14 _104795 _104796 p1 p2 s t) = (term15 _104795 _104796 p1 s p2 t).
Proof. exact (@lem4363590 _104795 _104796 p1 s p2 t). Qed.
Lemma lem4363594 {_104795 : Type'} (s : _104795 -> Prop) (f : type686 _104795) : (term207 _104795 s f) = (term207 _104795 s f).
Proof. exact (eq_refl (term207 _104795 s f)). Qed.
Lemma lem4363595 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (s : _104795 -> Prop) (p2 : _104796) (t : _104796 -> Prop) : (term336 _104795 _104796 f p1 p2 s t) = (term337 _104795 _104796 f p1 s p2 t).
Proof. exact (MK_COMB (@lem4363594 _104795 s f) (@lem4363591 _104795 _104796 p1 s p2 t)). Qed.
Lemma lem4363598 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term338 _104795 _104796 f p1 p2 t) = (term339 _104795 _104796 f p1 p2 t).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4363595 _104795 _104796 f p1 s p2 t)). Qed.
Lemma lem4363599 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4363600 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term335 _104795 _104796 f p1 p2 t) = (term340 _104795 _104796 f p1 p2 t).
Proof. exact (MK_COMB (@lem4363599 _104795) (@lem4363598 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363605 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term322 _104795 _104796 p1 p2 f t) = (term340 _104795 _104796 f p1 p2 t).
Proof. exact (TRANS (@lem4363581 _104795 _104796 f p1 p2 t) (@lem4363600 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363606 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : (term273 _104795 _104796 p1 p2 f t) = (term340 _104795 _104796 f p1 p2 t).
Proof. exact (TRANS (@lem4363559 _104795 _104796 p1 p2 f t) (@lem4363605 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363607 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (p2 : _104796) (t : _104796 -> Prop) : ((term272 _104795 _104796 p1 p2 f t) = (term273 _104795 _104796 p1 p2 f t)) = ((term281 _104795 _104796 p1 f p2 t) = (term340 _104795 _104796 f p1 p2 t)).
Proof. exact (MK_COMB (@lem4363506 _104795 _104796 p1 f p2 t) (@lem4363606 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363612 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term275 _104795 _104796 p1 f t) = (term341 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4363607 _104795 _104796 f p1 p2 t)). Qed.
Lemma lem4363613 {_104796 : Type'} : (@all _104796) = (@all _104796).
Proof. exact (eq_refl (@all _104796)). Qed.
Lemma lem4363614 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term277 _104795 _104796 p1 f t) = (term342 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4363613 _104796) (@lem4363612 _104795 _104796 f p1 t)). Qed.
Lemma lem4363621 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term279 _104795 _104796 f t) = (term343 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4363614 _104795 _104796 f p1 t)). Qed.
Lemma lem4363622 {_104795 : Type'} : (@all _104795) = (@all _104795).
Proof. exact (eq_refl (@all _104795)). Qed.
Lemma lem4363623 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term280 _104795 _104796 f t) = (term344 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4363622 _104795) (@lem4363621 _104795 _104796 f t)). Qed.
Lemma lem4363630 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term259 _104795 _104796 f t) = (term260 _104795 _104796 f t)) = (term344 _104795 _104796 f t).
Proof. exact (TRANS (@lem4363488 _104795 _104796 f t) (@lem4363623 _104795 _104796 f t)). Qed.
Lemma lem4363631 {_104795 _104796 : Type'} (f : type686 _104795) : (term345 _104795 _104796 f) = (term346 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4363630 _104795 _104796 f t)). Qed.
Lemma lem4363632 {_104796 : Type'} : (@all (_104796 -> Prop)) = (@all (_104796 -> Prop)).
Proof. exact (eq_refl (@all (_104796 -> Prop))). Qed.
Lemma lem4363633 {_104795 _104796 : Type'} (f : type686 _104795) : (term347 _104795 _104796 f) = (term348 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4363632 _104796) (@lem4363631 _104795 _104796 f)). Qed.
Lemma lem4363640 {_104795 _104796 : Type'} : (term349 _104795 _104796) = (term350 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4363633 _104795 _104796 f)). Qed.
Lemma lem4363641 {_104795 : Type'} : (@all ((_104795 -> Prop) -> Prop)) = (@all ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4363642 {_104795 _104796 : Type'} : (term351 _104795 _104796) = (term352 _104795 _104796).
Proof. exact (MK_COMB (@lem4363641 _104795) (@lem4363640 _104795 _104796)). Qed.
Lemma lem4363649 {_104757 _104758 _104795 _104796 : Type'} : (term353 _104757 _104758 _104795 _104796) = (term354 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4363440 _104757 _104758) (@lem4363642 _104795 _104796)). Qed.
Lemma lem4363652 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term355 _104717 _104718 _104757 _104758 _104795 _104796) = (term356 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4363228 _104717 _104718) (@lem4363649 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4363655 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term356 _104717 _104718 _104757 _104758 _104795 _104796) = (term355 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (SYM (@lem4363652 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4363781 {A : Type'} (s : type686 A) (x : A) : (term357 A x s) = (term358 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4363782 {_104717 : Type'} (s : type686 _104717) (x : _104717) : (term357 _104717 x s) = (term358 _104717 s x).
Proof. exact (@lem4363781 _104717 s x). Qed.
Lemma lem4363783 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term357 _104717 p1 f) = (term358 _104717 f p1).
Proof. exact (@lem4363782 _104717 f p1). Qed.
Lemma lem4363791 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363792 {_104717 : Type'} (P : type686 _104717) (x : _104717 -> Prop) : (@IN (_104717 -> Prop) x P) = (P x).
Proof. exact (@lem4363791 (_104717 -> Prop) P x). Qed.
Lemma lem4363793 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (@IN (_104717 -> Prop) t f) = (f t).
Proof. exact (@lem4363792 _104717 f t). Qed.
Lemma lem4363794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363795 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term207 _104717 t f) = (term359 _104717 f t).
Proof. exact (MK_COMB (@lem4363794) (@lem4363793 _104717 f t)). Qed.
Lemma lem4363797 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363798 {_104717 : Type'} (P : _104717 -> Prop) (x : _104717) : (@IN _104717 x P) = (P x).
Proof. exact (@lem4363797 _104717 P x). Qed.
Lemma lem4363799 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (@IN _104717 p1 t) = (t p1).
Proof. exact (@lem4363798 _104717 t p1). Qed.
Lemma lem4363800 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term360 _104717 f p1 t) = (term361 _104717 f t p1).
Proof. exact (MK_COMB (@lem4363795 _104717 f t) (@lem4363799 _104717 t p1)). Qed.
Lemma lem4363803 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term362 _104717 f p1) = (term363 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4363800 _104717 f t p1)). Qed.
Lemma lem4363804 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4363805 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term358 _104717 f p1) = (term364 _104717 f p1).
Proof. exact (MK_COMB (@lem4363804 _104717) (@lem4363803 _104717 f p1)). Qed.
Lemma lem4363810 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term357 _104717 p1 f) = (term364 _104717 f p1).
Proof. exact (TRANS (@lem4363783 _104717 f p1) (@lem4363805 _104717 f p1)). Qed.
Lemma lem4363811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363812 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term365 _104717 p1 f) = (term366 _104717 f p1).
Proof. exact (MK_COMB (@lem4363811) (@lem4363810 _104717 f p1)). Qed.
Lemma lem4363814 {A : Type'} (s : type686 A) (x : A) : (term357 A x s) = (term358 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4363815 {_104718 : Type'} (s : type686 _104718) (x : _104718) : (term357 _104718 x s) = (term358 _104718 s x).
Proof. exact (@lem4363814 _104718 s x). Qed.
Lemma lem4363816 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term357 _104718 p2 g) = (term358 _104718 g p2).
Proof. exact (@lem4363815 _104718 g p2). Qed.
Lemma lem4363824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363825 {_104718 : Type'} (P : type686 _104718) (x : _104718 -> Prop) : (@IN (_104718 -> Prop) x P) = (P x).
Proof. exact (@lem4363824 (_104718 -> Prop) P x). Qed.
Lemma lem4363826 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (@IN (_104718 -> Prop) t g) = (g t).
Proof. exact (@lem4363825 _104718 g t). Qed.
Lemma lem4363827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363828 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (term207 _104718 t g) = (term359 _104718 g t).
Proof. exact (MK_COMB (@lem4363827) (@lem4363826 _104718 g t)). Qed.
Lemma lem4363830 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363831 {_104718 : Type'} (P : _104718 -> Prop) (x : _104718) : (@IN _104718 x P) = (P x).
Proof. exact (@lem4363830 _104718 P x). Qed.
Lemma lem4363832 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (@IN _104718 p2 t) = (t p2).
Proof. exact (@lem4363831 _104718 t p2). Qed.
Lemma lem4363833 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term360 _104718 g p2 t) = (term361 _104718 g t p2).
Proof. exact (MK_COMB (@lem4363828 _104718 g t) (@lem4363832 _104718 t p2)). Qed.
Lemma lem4363836 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term362 _104718 g p2) = (term363 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4363833 _104718 g t p2)). Qed.
Lemma lem4363837 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4363838 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term358 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (MK_COMB (@lem4363837 _104718) (@lem4363836 _104718 g p2)). Qed.
Lemma lem4363843 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term357 _104718 p2 g) = (term364 _104718 g p2).
Proof. exact (TRANS (@lem4363816 _104718 g p2) (@lem4363838 _104718 g p2)). Qed.
Lemma lem4363844 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term65 _104717 _104718 p1 f p2 g) = (term367 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4363812 _104717 f p1) (@lem4363843 _104718 g p2)). Qed.
Lemma lem4363847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4363848 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term67 _104717 _104718 p1 f p2 g) = (term368 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4363847) (@lem4363844 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4363862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363863 {_104717 : Type'} (P : type686 _104717) (x : _104717 -> Prop) : (@IN (_104717 -> Prop) x P) = (P x).
Proof. exact (@lem4363862 (_104717 -> Prop) P x). Qed.
Lemma lem4363864 {_104717 : Type'} (f : type686 _104717) (s : _104717 -> Prop) : (@IN (_104717 -> Prop) s f) = (f s).
Proof. exact (@lem4363863 _104717 f s). Qed.
Lemma lem4363865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363866 {_104717 : Type'} (f : type686 _104717) (s : _104717 -> Prop) : (term207 _104717 s f) = (term359 _104717 f s).
Proof. exact (MK_COMB (@lem4363865) (@lem4363864 _104717 f s)). Qed.
Lemma lem4363868 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363869 {_104718 : Type'} (P : type686 _104718) (x : _104718 -> Prop) : (@IN (_104718 -> Prop) x P) = (P x).
Proof. exact (@lem4363868 (_104718 -> Prop) P x). Qed.
Lemma lem4363870 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (@IN (_104718 -> Prop) t g) = (g t).
Proof. exact (@lem4363869 _104718 g t). Qed.
Lemma lem4363871 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term77 _104717 _104718 s f t g) = (term369 _104717 _104718 f s g t).
Proof. exact (MK_COMB (@lem4363866 _104717 f s) (@lem4363870 _104718 g t)). Qed.
Lemma lem4363874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363875 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term97 _104717 _104718 s f t g) = (term370 _104717 _104718 f s g t).
Proof. exact (MK_COMB (@lem4363874) (@lem4363871 _104717 _104718 f s g t)). Qed.
Lemma lem4363879 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363880 {_104717 : Type'} (P : _104717 -> Prop) (x : _104717) : (@IN _104717 x P) = (P x).
Proof. exact (@lem4363879 _104717 P x). Qed.
Lemma lem4363881 {_104717 : Type'} (s : _104717 -> Prop) (p1 : _104717) : (@IN _104717 p1 s) = (s p1).
Proof. exact (@lem4363880 _104717 s p1). Qed.
Lemma lem4363882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363883 {_104717 : Type'} (s : _104717 -> Prop) (p1 : _104717) : (term371 _104717 p1 s) = (term372 _104717 s p1).
Proof. exact (MK_COMB (@lem4363882) (@lem4363881 _104717 s p1)). Qed.
Lemma lem4363885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363886 {_104718 : Type'} (P : _104718 -> Prop) (x : _104718) : (@IN _104718 x P) = (P x).
Proof. exact (@lem4363885 _104718 P x). Qed.
Lemma lem4363887 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (@IN _104718 p2 t) = (t p2).
Proof. exact (@lem4363886 _104718 t p2). Qed.
Lemma lem4363888 {_104717 _104718 : Type'} (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term15 _104717 _104718 p1 s p2 t) = (term373 _104717 _104718 s p1 t p2).
Proof. exact (MK_COMB (@lem4363883 _104717 s p1) (@lem4363887 _104718 t p2)). Qed.
Lemma lem4363891 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term137 _104717 _104718 f g p1 s p2 t) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4363875 _104717 _104718 f s g t) (@lem4363888 _104717 _104718 s p1 t p2)). Qed.
Lemma lem4363894 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term139 _104717 _104718 f g p1 s p2) = (term375 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4363891 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4363895 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4363896 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term141 _104717 _104718 f g p1 s p2) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4363895 _104718) (@lem4363894 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4363901 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term143 _104717 _104718 f g p1 p2) = (term377 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4363896 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4363902 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4363903 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term144 _104717 _104718 f g p1 p2) = (term378 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4363902 _104717) (@lem4363901 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363908 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term65 _104717 _104718 p1 f p2 g) = (term144 _104717 _104718 f g p1 p2)) = ((term367 _104717 _104718 f p1 g p2) = (term378 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4363848 _104717 _104718 f p1 g p2) (@lem4363903 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363911 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term145 _104717 _104718 f g p1) = (term379 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4363908 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4363912 {_104718 : Type'} : (@all _104718) = (@all _104718).
Proof. exact (eq_refl (@all _104718)). Qed.
Lemma lem4363913 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term146 _104717 _104718 f g p1) = (term380 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4363912 _104718) (@lem4363911 _104717 _104718 f g p1)). Qed.
Lemma lem4363918 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term147 _104717 _104718 f g) = (term381 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4363913 _104717 _104718 f g p1)). Qed.
Lemma lem4363919 {_104717 : Type'} : (@all _104717) = (@all _104717).
Proof. exact (eq_refl (@all _104717)). Qed.
Lemma lem4363920 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term148 _104717 _104718 f g) = (term382 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4363919 _104717) (@lem4363918 _104717 _104718 f g)). Qed.
Lemma lem4363925 {_104717 _104718 : Type'} (f : type686 _104717) : (term150 _104717 _104718 f) = (term383 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4363920 _104717 _104718 f g)). Qed.
Lemma lem4363926 {_104718 : Type'} : (@all ((_104718 -> Prop) -> Prop)) = (@all ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4363927 {_104717 _104718 : Type'} (f : type686 _104717) : (term152 _104717 _104718 f) = (term384 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4363926 _104718) (@lem4363925 _104717 _104718 f)). Qed.
Lemma lem4363932 {_104717 _104718 : Type'} : (term154 _104717 _104718) = (term385 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4363927 _104717 _104718 f)). Qed.
Lemma lem4363933 {_104717 : Type'} : (@all ((_104717 -> Prop) -> Prop)) = (@all ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4363934 {_104717 _104718 : Type'} : (term156 _104717 _104718) = (term386 _104717 _104718).
Proof. exact (MK_COMB (@lem4363933 _104717) (@lem4363932 _104717 _104718)). Qed.
Lemma lem4363939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363940 {_104717 _104718 : Type'} : (term158 _104717 _104718) = (term387 _104717 _104718).
Proof. exact (MK_COMB (@lem4363939) (@lem4363934 _104717 _104718)). Qed.
Lemma lem4363964 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363965 {_104757 : Type'} (P : _104757 -> Prop) (x : _104757) : (@IN _104757 x P) = (P x).
Proof. exact (@lem4363964 _104757 P x). Qed.
Lemma lem4363966 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (@IN _104757 p1 s) = (s p1).
Proof. exact (@lem4363965 _104757 s p1). Qed.
Lemma lem4363967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363968 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term371 _104757 p1 s) = (term372 _104757 s p1).
Proof. exact (MK_COMB (@lem4363967) (@lem4363966 _104757 s p1)). Qed.
Lemma lem4363970 {A : Type'} (s : type686 A) (x : A) : (term357 A x s) = (term358 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4363971 {_104758 : Type'} (s : type686 _104758) (x : _104758) : (term357 _104758 x s) = (term358 _104758 s x).
Proof. exact (@lem4363970 _104758 s x). Qed.
Lemma lem4363972 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term357 _104758 p2 f) = (term358 _104758 f p2).
Proof. exact (@lem4363971 _104758 f p2). Qed.
Lemma lem4363980 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363981 {_104758 : Type'} (P : type686 _104758) (x : _104758 -> Prop) : (@IN (_104758 -> Prop) x P) = (P x).
Proof. exact (@lem4363980 (_104758 -> Prop) P x). Qed.
Lemma lem4363982 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) : (@IN (_104758 -> Prop) t f) = (f t).
Proof. exact (@lem4363981 _104758 f t). Qed.
Lemma lem4363983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4363984 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) : (term207 _104758 t f) = (term359 _104758 f t).
Proof. exact (MK_COMB (@lem4363983) (@lem4363982 _104758 f t)). Qed.
Lemma lem4363986 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4363987 {_104758 : Type'} (P : _104758 -> Prop) (x : _104758) : (@IN _104758 x P) = (P x).
Proof. exact (@lem4363986 _104758 P x). Qed.
Lemma lem4363988 {_104758 : Type'} (t : _104758 -> Prop) (p2 : _104758) : (@IN _104758 p2 t) = (t p2).
Proof. exact (@lem4363987 _104758 t p2). Qed.
Lemma lem4363989 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term360 _104758 f p2 t) = (term361 _104758 f t p2).
Proof. exact (MK_COMB (@lem4363984 _104758 f t) (@lem4363988 _104758 t p2)). Qed.
Lemma lem4363992 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term362 _104758 f p2) = (term363 _104758 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4363989 _104758 f t p2)). Qed.
Lemma lem4363993 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4363994 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term358 _104758 f p2) = (term364 _104758 f p2).
Proof. exact (MK_COMB (@lem4363993 _104758) (@lem4363992 _104758 f p2)). Qed.
Lemma lem4363999 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term357 _104758 p2 f) = (term364 _104758 f p2).
Proof. exact (TRANS (@lem4363972 _104758 f p2) (@lem4363994 _104758 f p2)). Qed.
Lemma lem4364000 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term181 _104757 _104758 p1 s p2 f) = (term388 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4363968 _104757 s p1) (@lem4363999 _104758 f p2)). Qed.
Lemma lem4364003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4364004 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term183 _104757 _104758 p1 s p2 f) = (term389 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4364003) (@lem4364000 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4364012 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364013 {_104758 : Type'} (P : type686 _104758) (x : _104758 -> Prop) : (@IN (_104758 -> Prop) x P) = (P x).
Proof. exact (@lem4364012 (_104758 -> Prop) P x). Qed.
Lemma lem4364014 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) : (@IN (_104758 -> Prop) t f) = (f t).
Proof. exact (@lem4364013 _104758 f t). Qed.
Lemma lem4364015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364016 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) : (term207 _104758 t f) = (term359 _104758 f t).
Proof. exact (MK_COMB (@lem4364015) (@lem4364014 _104758 f t)). Qed.
Lemma lem4364020 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364021 {_104757 : Type'} (P : _104757 -> Prop) (x : _104757) : (@IN _104757 x P) = (P x).
Proof. exact (@lem4364020 _104757 P x). Qed.
Lemma lem4364022 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (@IN _104757 p1 s) = (s p1).
Proof. exact (@lem4364021 _104757 s p1). Qed.
Lemma lem4364023 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364024 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term371 _104757 p1 s) = (term372 _104757 s p1).
Proof. exact (MK_COMB (@lem4364023) (@lem4364022 _104757 s p1)). Qed.
Lemma lem4364026 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364027 {_104758 : Type'} (P : _104758 -> Prop) (x : _104758) : (@IN _104758 x P) = (P x).
Proof. exact (@lem4364026 _104758 P x). Qed.
Lemma lem4364028 {_104758 : Type'} (t : _104758 -> Prop) (p2 : _104758) : (@IN _104758 p2 t) = (t p2).
Proof. exact (@lem4364027 _104758 t p2). Qed.
Lemma lem4364029 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term15 _104757 _104758 p1 s p2 t) = (term373 _104757 _104758 s p1 t p2).
Proof. exact (MK_COMB (@lem4364024 _104757 s p1) (@lem4364028 _104758 t p2)). Qed.
Lemma lem4364032 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term241 _104757 _104758 f p1 s p2 t) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4364016 _104758 f t) (@lem4364029 _104757 _104758 s p1 t p2)). Qed.
Lemma lem4364035 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term243 _104757 _104758 f p1 s p2) = (term391 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4364032 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4364036 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4364037 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term244 _104757 _104758 f p1 s p2) = (term392 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4364036 _104758) (@lem4364035 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364042 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term181 _104757 _104758 p1 s p2 f) = (term244 _104757 _104758 f p1 s p2)) = ((term388 _104757 _104758 s p1 f p2) = (term392 _104757 _104758 f s p1 p2)).
Proof. exact (MK_COMB (@lem4364004 _104757 _104758 s p1 f p2) (@lem4364037 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364045 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term245 _104757 _104758 f p1 s) = (term393 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4364042 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364046 {_104758 : Type'} : (@all _104758) = (@all _104758).
Proof. exact (eq_refl (@all _104758)). Qed.
Lemma lem4364047 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term246 _104757 _104758 f p1 s) = (term394 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4364046 _104758) (@lem4364045 _104757 _104758 f s p1)). Qed.
Lemma lem4364052 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term247 _104757 _104758 f s) = (term395 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4364047 _104757 _104758 f s p1)). Qed.
Lemma lem4364053 {_104757 : Type'} : (@all _104757) = (@all _104757).
Proof. exact (eq_refl (@all _104757)). Qed.
Lemma lem4364054 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term248 _104757 _104758 f s) = (term396 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4364053 _104757) (@lem4364052 _104757 _104758 f s)). Qed.
Lemma lem4364059 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term250 _104757 _104758 s) = (term397 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4364054 _104757 _104758 f s)). Qed.
Lemma lem4364060 {_104758 : Type'} : (@all ((_104758 -> Prop) -> Prop)) = (@all ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4364061 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term252 _104757 _104758 s) = (term398 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4364060 _104758) (@lem4364059 _104757 _104758 s)). Qed.
Lemma lem4364066 {_104757 _104758 : Type'} : (term254 _104757 _104758) = (term399 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4364061 _104757 _104758 s)). Qed.
Lemma lem4364067 {_104757 : Type'} : (@all (_104757 -> Prop)) = (@all (_104757 -> Prop)).
Proof. exact (eq_refl (@all (_104757 -> Prop))). Qed.
Lemma lem4364068 {_104757 _104758 : Type'} : (term256 _104757 _104758) = (term400 _104757 _104758).
Proof. exact (MK_COMB (@lem4364067 _104757) (@lem4364066 _104757 _104758)). Qed.
Lemma lem4364073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364074 {_104757 _104758 : Type'} : (term258 _104757 _104758) = (term401 _104757 _104758).
Proof. exact (MK_COMB (@lem4364073) (@lem4364068 _104757 _104758)). Qed.
Lemma lem4364096 {A : Type'} (s : type686 A) (x : A) : (term357 A x s) = (term358 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4364097 {_104795 : Type'} (s : type686 _104795) (x : _104795) : (term357 _104795 x s) = (term358 _104795 s x).
Proof. exact (@lem4364096 _104795 s x). Qed.
Lemma lem4364098 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term357 _104795 p1 f) = (term358 _104795 f p1).
Proof. exact (@lem4364097 _104795 f p1). Qed.
Lemma lem4364106 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364107 {_104795 : Type'} (P : type686 _104795) (x : _104795 -> Prop) : (@IN (_104795 -> Prop) x P) = (P x).
Proof. exact (@lem4364106 (_104795 -> Prop) P x). Qed.
Lemma lem4364108 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) : (@IN (_104795 -> Prop) t f) = (f t).
Proof. exact (@lem4364107 _104795 f t). Qed.
Lemma lem4364109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364110 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) : (term207 _104795 t f) = (term359 _104795 f t).
Proof. exact (MK_COMB (@lem4364109) (@lem4364108 _104795 f t)). Qed.
Lemma lem4364112 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364113 {_104795 : Type'} (P : _104795 -> Prop) (x : _104795) : (@IN _104795 x P) = (P x).
Proof. exact (@lem4364112 _104795 P x). Qed.
Lemma lem4364114 {_104795 : Type'} (t : _104795 -> Prop) (p1 : _104795) : (@IN _104795 p1 t) = (t p1).
Proof. exact (@lem4364113 _104795 t p1). Qed.
Lemma lem4364115 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term360 _104795 f p1 t) = (term361 _104795 f t p1).
Proof. exact (MK_COMB (@lem4364110 _104795 f t) (@lem4364114 _104795 t p1)). Qed.
Lemma lem4364118 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term362 _104795 f p1) = (term363 _104795 f p1).
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4364115 _104795 f t p1)). Qed.
Lemma lem4364119 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4364120 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term358 _104795 f p1) = (term364 _104795 f p1).
Proof. exact (MK_COMB (@lem4364119 _104795) (@lem4364118 _104795 f p1)). Qed.
Lemma lem4364125 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term357 _104795 p1 f) = (term364 _104795 f p1).
Proof. exact (TRANS (@lem4364098 _104795 f p1) (@lem4364120 _104795 f p1)). Qed.
Lemma lem4364126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364127 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term365 _104795 p1 f) = (term366 _104795 f p1).
Proof. exact (MK_COMB (@lem4364126) (@lem4364125 _104795 f p1)). Qed.
Lemma lem4364129 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364130 {_104796 : Type'} (P : _104796 -> Prop) (x : _104796) : (@IN _104796 x P) = (P x).
Proof. exact (@lem4364129 _104796 P x). Qed.
Lemma lem4364131 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (@IN _104796 p2 t) = (t p2).
Proof. exact (@lem4364130 _104796 t p2). Qed.
Lemma lem4364132 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term281 _104795 _104796 p1 f p2 t) = (term402 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364127 _104795 f p1) (@lem4364131 _104796 t p2)). Qed.
Lemma lem4364135 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4364136 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term283 _104795 _104796 p1 f p2 t) = (term403 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364135) (@lem4364132 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364144 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364145 {_104795 : Type'} (P : type686 _104795) (x : _104795 -> Prop) : (@IN (_104795 -> Prop) x P) = (P x).
Proof. exact (@lem4364144 (_104795 -> Prop) P x). Qed.
Lemma lem4364146 {_104795 : Type'} (f : type686 _104795) (s : _104795 -> Prop) : (@IN (_104795 -> Prop) s f) = (f s).
Proof. exact (@lem4364145 _104795 f s). Qed.
Lemma lem4364147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364148 {_104795 : Type'} (f : type686 _104795) (s : _104795 -> Prop) : (term207 _104795 s f) = (term359 _104795 f s).
Proof. exact (MK_COMB (@lem4364147) (@lem4364146 _104795 f s)). Qed.
Lemma lem4364152 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364153 {_104795 : Type'} (P : _104795 -> Prop) (x : _104795) : (@IN _104795 x P) = (P x).
Proof. exact (@lem4364152 _104795 P x). Qed.
Lemma lem4364154 {_104795 : Type'} (s : _104795 -> Prop) (p1 : _104795) : (@IN _104795 p1 s) = (s p1).
Proof. exact (@lem4364153 _104795 s p1). Qed.
Lemma lem4364155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364156 {_104795 : Type'} (s : _104795 -> Prop) (p1 : _104795) : (term371 _104795 p1 s) = (term372 _104795 s p1).
Proof. exact (MK_COMB (@lem4364155) (@lem4364154 _104795 s p1)). Qed.
Lemma lem4364158 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4364159 {_104796 : Type'} (P : _104796 -> Prop) (x : _104796) : (@IN _104796 x P) = (P x).
Proof. exact (@lem4364158 _104796 P x). Qed.
Lemma lem4364160 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (@IN _104796 p2 t) = (t p2).
Proof. exact (@lem4364159 _104796 t p2). Qed.
Lemma lem4364161 {_104795 _104796 : Type'} (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term15 _104795 _104796 p1 s p2 t) = (term373 _104795 _104796 s p1 t p2).
Proof. exact (MK_COMB (@lem4364156 _104795 s p1) (@lem4364160 _104796 t p2)). Qed.
Lemma lem4364164 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term337 _104795 _104796 f p1 s p2 t) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4364148 _104795 f s) (@lem4364161 _104795 _104796 s p1 t p2)). Qed.
Lemma lem4364167 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term339 _104795 _104796 f p1 p2 t) = (term405 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4364164 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4364168 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4364169 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term340 _104795 _104796 f p1 p2 t) = (term406 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364168 _104795) (@lem4364167 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364174 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term281 _104795 _104796 p1 f p2 t) = (term340 _104795 _104796 f p1 p2 t)) = ((term402 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4364136 _104795 _104796 f p1 t p2) (@lem4364169 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364177 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term341 _104795 _104796 f p1 t) = (term407 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4364174 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364178 {_104796 : Type'} : (@all _104796) = (@all _104796).
Proof. exact (eq_refl (@all _104796)). Qed.
Lemma lem4364179 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term342 _104795 _104796 f p1 t) = (term408 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4364178 _104796) (@lem4364177 _104795 _104796 f p1 t)). Qed.
Lemma lem4364184 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term343 _104795 _104796 f t) = (term409 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4364179 _104795 _104796 f p1 t)). Qed.
Lemma lem4364185 {_104795 : Type'} : (@all _104795) = (@all _104795).
Proof. exact (eq_refl (@all _104795)). Qed.
Lemma lem4364186 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term344 _104795 _104796 f t) = (term410 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4364185 _104795) (@lem4364184 _104795 _104796 f t)). Qed.
Lemma lem4364191 {_104795 _104796 : Type'} (f : type686 _104795) : (term346 _104795 _104796 f) = (term411 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4364186 _104795 _104796 f t)). Qed.
Lemma lem4364192 {_104796 : Type'} : (@all (_104796 -> Prop)) = (@all (_104796 -> Prop)).
Proof. exact (eq_refl (@all (_104796 -> Prop))). Qed.
Lemma lem4364193 {_104795 _104796 : Type'} (f : type686 _104795) : (term348 _104795 _104796 f) = (term412 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4364192 _104796) (@lem4364191 _104795 _104796 f)). Qed.
Lemma lem4364198 {_104795 _104796 : Type'} : (term350 _104795 _104796) = (term413 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4364193 _104795 _104796 f)). Qed.
Lemma lem4364199 {_104795 : Type'} : (@all ((_104795 -> Prop) -> Prop)) = (@all ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4364200 {_104795 _104796 : Type'} : (term352 _104795 _104796) = (term414 _104795 _104796).
Proof. exact (MK_COMB (@lem4364199 _104795) (@lem4364198 _104795 _104796)). Qed.
Lemma lem4364205 {_104757 _104758 _104795 _104796 : Type'} : (term354 _104757 _104758 _104795 _104796) = (term415 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4364074 _104757 _104758) (@lem4364200 _104795 _104796)). Qed.
Lemma lem4364208 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term356 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4363940 _104717 _104718) (@lem4364205 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364211 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term416 _104717 _104718 _104757 _104758 _104795 _104796) = (term356 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (SYM (@lem4364208 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364213 (p : Prop) : p = (term417 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4364214 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term416 _104717 _104718 _104757 _104758 _104795 _104796) = (term418 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem4364213 (term416 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364215 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term418 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (SYM (@lem4364214 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364216 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : term419 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364219 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term418 _104717 _104718 _104757 _104758 _104795 _104796) : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364220 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term418 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4364219 _104717 _104718 _104757 _104758 _104795 _104796 h0). Qed.
Lemma lem4364221 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term420 _104717 _104718 _104757 _104758 _104795 _104796) : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364222 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term418 _104717 _104718 _104757 _104758 _104795 _104796) : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364223 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term418 _104717 _104718 _104757 _104758 _104795 _104796) (h2 : term420 _104717 _104718 _104757 _104758 _104795 _104796) : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (@lem4364221 _104717 _104718 _104757 _104758 _104795 _104796 h2 (@lem4364222 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4364224 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term418 _104717 _104718 _104757 _104758 _104795 _104796) : term421 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term420 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4364223 _104717 _104718 _104757 _104758 _104795 _104796 h1 h0). Qed.
Lemma lem4364225 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term420 _104717 _104718 _104757 _104758 _104795 _104796) : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364226 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term418 _104717 _104718 _104757 _104758 _104795 _104796) (h2 : term420 _104717 _104718 _104757 _104758 _104795 _104796) : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (@lem4364224 _104717 _104718 _104757 _104758 _104795 _104796 h1 (@lem4364225 _104717 _104718 _104757 _104758 _104795 _104796 h2)). Qed.
Lemma lem4364227 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term420 _104717 _104718 _104757 _104758 _104795 _104796) : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term418 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4364226 _104717 _104718 _104757 _104758 _104795 _104796 h0 h1). Qed.
Lemma lem4364228 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term422 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term420 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4364227 _104717 _104718 _104757 _104758 _104795 _104796 h0). Qed.
Lemma lem4364231 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (@lem4364228 _104717 _104718 _104757 _104758 _104795 _104796 (@lem4364220 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364232 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term420 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (@lem4364231 _104717 _104718 _104757 _104758 _104795 _104796). Qed.
Lemma lem4364234 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4364235 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term418 _104717 _104718 _104757 _104758 _104795 _104796) = (term423 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem4364234 (term419 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364237 (t : Prop) : (term424 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4364238 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term423 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem4364237 (term416 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364543 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term418 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4364235 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4364238 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364552 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term404 _104795 _104796 f s p1 t p2) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term404 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4364553 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term405 _104795 _104796 f p1 t p2) = (term405 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4364552 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4364554 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4364555 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term406 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364554 _104795) (@lem4364553 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364556 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4364561 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term361 _104795 f t p1) = (term361 _104795 f t p1).
Proof. exact (eq_refl (term361 _104795 f t p1)). Qed.
Lemma lem4364562 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term363 _104795 f p1) = (term363 _104795 f p1).
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4364561 _104795 f t p1)). Qed.
Lemma lem4364563 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4364564 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term364 _104795 f p1) = (term364 _104795 f p1).
Proof. exact (MK_COMB (@lem4364563 _104795) (@lem4364562 _104795 f p1)). Qed.
Lemma lem4364565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364566 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term366 _104795 f p1) = (term366 _104795 f p1).
Proof. exact (MK_COMB (@lem4364565) (@lem4364564 _104795 f p1)). Qed.
Lemma lem4364567 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term402 _104795 _104796 f p1 t p2) = (term402 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364566 _104795 f p1) (@lem4364556 _104796 t p2)). Qed.
Lemma lem4364568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4364569 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term403 _104795 _104796 f p1 t p2) = (term403 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4364568) (@lem4364567 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364570 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term402 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2)) = ((term402 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4364569 _104795 _104796 f p1 t p2) (@lem4364555 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364571 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term407 _104795 _104796 f p1 t) = (term407 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4364570 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4364572 {_104796 : Type'} : (@all _104796) = (@all _104796).
Proof. exact (eq_refl (@all _104796)). Qed.
Lemma lem4364573 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term408 _104795 _104796 f p1 t) = (term408 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4364572 _104796) (@lem4364571 _104795 _104796 f p1 t)). Qed.
Lemma lem4364574 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term409 _104795 _104796 f t) = (term409 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4364573 _104795 _104796 f p1 t)). Qed.
Lemma lem4364575 {_104795 : Type'} : (@all _104795) = (@all _104795).
Proof. exact (eq_refl (@all _104795)). Qed.
Lemma lem4364576 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term410 _104795 _104796 f t) = (term410 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4364575 _104795) (@lem4364574 _104795 _104796 f t)). Qed.
Lemma lem4364577 {_104795 _104796 : Type'} (f : type686 _104795) : (term411 _104795 _104796 f) = (term411 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4364576 _104795 _104796 f t)). Qed.
Lemma lem4364578 {_104796 : Type'} : (@all (_104796 -> Prop)) = (@all (_104796 -> Prop)).
Proof. exact (eq_refl (@all (_104796 -> Prop))). Qed.
Lemma lem4364579 {_104795 _104796 : Type'} (f : type686 _104795) : (term412 _104795 _104796 f) = (term412 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4364578 _104796) (@lem4364577 _104795 _104796 f)). Qed.
Lemma lem4364580 {_104795 _104796 : Type'} : (term413 _104795 _104796) = (term413 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4364579 _104795 _104796 f)). Qed.
Lemma lem4364581 {_104795 : Type'} : (@all ((_104795 -> Prop) -> Prop)) = (@all ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4364582 {_104795 _104796 : Type'} : (term414 _104795 _104796) = (term414 _104795 _104796).
Proof. exact (MK_COMB (@lem4364581 _104795) (@lem4364580 _104795 _104796)). Qed.
Lemma lem4364591 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term390 _104757 _104758 f s p1 t p2) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term390 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4364592 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term391 _104757 _104758 f s p1 p2) = (term391 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4364591 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4364593 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4364594 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term392 _104757 _104758 f s p1 p2) = (term392 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4364593 _104758) (@lem4364592 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364599 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term361 _104758 f t p2) = (term361 _104758 f t p2).
Proof. exact (eq_refl (term361 _104758 f t p2)). Qed.
Lemma lem4364600 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term363 _104758 f p2) = (term363 _104758 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4364599 _104758 f t p2)). Qed.
Lemma lem4364601 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4364602 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term364 _104758 f p2) = (term364 _104758 f p2).
Proof. exact (MK_COMB (@lem4364601 _104758) (@lem4364600 _104758 f p2)). Qed.
Lemma lem4364605 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term372 _104757 s p1) = (term372 _104757 s p1).
Proof. exact (eq_refl (term372 _104757 s p1)). Qed.
Lemma lem4364606 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term388 _104757 _104758 s p1 f p2) = (term388 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4364605 _104757 s p1) (@lem4364602 _104758 f p2)). Qed.
Lemma lem4364607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4364608 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term389 _104757 _104758 s p1 f p2) = (term389 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4364607) (@lem4364606 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4364609 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term388 _104757 _104758 s p1 f p2) = (term392 _104757 _104758 f s p1 p2)) = ((term388 _104757 _104758 s p1 f p2) = (term392 _104757 _104758 f s p1 p2)).
Proof. exact (MK_COMB (@lem4364608 _104757 _104758 s p1 f p2) (@lem4364594 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364610 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term393 _104757 _104758 f s p1) = (term393 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4364609 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4364611 {_104758 : Type'} : (@all _104758) = (@all _104758).
Proof. exact (eq_refl (@all _104758)). Qed.
Lemma lem4364612 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term394 _104757 _104758 f s p1) = (term394 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4364611 _104758) (@lem4364610 _104757 _104758 f s p1)). Qed.
Lemma lem4364613 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term395 _104757 _104758 f s) = (term395 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4364612 _104757 _104758 f s p1)). Qed.
Lemma lem4364614 {_104757 : Type'} : (@all _104757) = (@all _104757).
Proof. exact (eq_refl (@all _104757)). Qed.
Lemma lem4364615 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term396 _104757 _104758 f s) = (term396 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4364614 _104757) (@lem4364613 _104757 _104758 f s)). Qed.
Lemma lem4364616 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term397 _104757 _104758 s) = (term397 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4364615 _104757 _104758 f s)). Qed.
Lemma lem4364617 {_104758 : Type'} : (@all ((_104758 -> Prop) -> Prop)) = (@all ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4364618 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term398 _104757 _104758 s) = (term398 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4364617 _104758) (@lem4364616 _104757 _104758 s)). Qed.
Lemma lem4364619 {_104757 _104758 : Type'} : (term399 _104757 _104758) = (term399 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4364618 _104757 _104758 s)). Qed.
Lemma lem4364620 {_104757 : Type'} : (@all (_104757 -> Prop)) = (@all (_104757 -> Prop)).
Proof. exact (eq_refl (@all (_104757 -> Prop))). Qed.
Lemma lem4364621 {_104757 _104758 : Type'} : (term400 _104757 _104758) = (term400 _104757 _104758).
Proof. exact (MK_COMB (@lem4364620 _104757) (@lem4364619 _104757 _104758)). Qed.
Lemma lem4364622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364623 {_104757 _104758 : Type'} : (term401 _104757 _104758) = (term401 _104757 _104758).
Proof. exact (MK_COMB (@lem4364622) (@lem4364621 _104757 _104758)). Qed.
Lemma lem4364624 {_104757 _104758 _104795 _104796 : Type'} : (term415 _104757 _104758 _104795 _104796) = (term415 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4364623 _104757 _104758) (@lem4364582 _104795 _104796)). Qed.
Lemma lem4364637 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term374 _104717 _104718 f g s p1 t p2) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term374 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364638 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term375 _104717 _104718 f g s p1 p2) = (term375 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364637 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364639 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4364640 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term376 _104717 _104718 f g s p1 p2) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4364639 _104718) (@lem4364638 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364641 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term377 _104717 _104718 f g p1 p2) = (term377 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4364640 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364642 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4364643 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term378 _104717 _104718 f g p1 p2) = (term378 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364642 _104717) (@lem4364641 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364648 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term361 _104718 g t p2) = (term361 _104718 g t p2).
Proof. exact (eq_refl (term361 _104718 g t p2)). Qed.
Lemma lem4364649 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term363 _104718 g p2) = (term363 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364648 _104718 g t p2)). Qed.
Lemma lem4364650 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4364651 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term364 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (MK_COMB (@lem4364650 _104718) (@lem4364649 _104718 g p2)). Qed.
Lemma lem4364656 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term361 _104717 f t p1) = (term361 _104717 f t p1).
Proof. exact (eq_refl (term361 _104717 f t p1)). Qed.
Lemma lem4364657 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term363 _104717 f p1) = (term363 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4364656 _104717 f t p1)). Qed.
Lemma lem4364658 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4364659 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term364 _104717 f p1) = (term364 _104717 f p1).
Proof. exact (MK_COMB (@lem4364658 _104717) (@lem4364657 _104717 f p1)). Qed.
Lemma lem4364660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364661 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term366 _104717 f p1) = (term366 _104717 f p1).
Proof. exact (MK_COMB (@lem4364660) (@lem4364659 _104717 f p1)). Qed.
Lemma lem4364662 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term367 _104717 _104718 f p1 g p2) = (term367 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364661 _104717 f p1) (@lem4364651 _104718 g p2)). Qed.
Lemma lem4364663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4364664 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term368 _104717 _104718 f p1 g p2) = (term368 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364663) (@lem4364662 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4364665 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term367 _104717 _104718 f p1 g p2) = (term378 _104717 _104718 f g p1 p2)) = ((term367 _104717 _104718 f p1 g p2) = (term378 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4364664 _104717 _104718 f p1 g p2) (@lem4364643 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364666 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term379 _104717 _104718 f g p1) = (term379 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4364665 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364667 {_104718 : Type'} : (@all _104718) = (@all _104718).
Proof. exact (eq_refl (@all _104718)). Qed.
Lemma lem4364668 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term380 _104717 _104718 f g p1) = (term380 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4364667 _104718) (@lem4364666 _104717 _104718 f g p1)). Qed.
Lemma lem4364669 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term381 _104717 _104718 f g) = (term381 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4364668 _104717 _104718 f g p1)). Qed.
Lemma lem4364670 {_104717 : Type'} : (@all _104717) = (@all _104717).
Proof. exact (eq_refl (@all _104717)). Qed.
Lemma lem4364671 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term382 _104717 _104718 f g) = (term382 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4364670 _104717) (@lem4364669 _104717 _104718 f g)). Qed.
Lemma lem4364672 {_104717 _104718 : Type'} (f : type686 _104717) : (term383 _104717 _104718 f) = (term383 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4364671 _104717 _104718 f g)). Qed.
Lemma lem4364673 {_104718 : Type'} : (@all ((_104718 -> Prop) -> Prop)) = (@all ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4364674 {_104717 _104718 : Type'} (f : type686 _104717) : (term384 _104717 _104718 f) = (term384 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4364673 _104718) (@lem4364672 _104717 _104718 f)). Qed.
Lemma lem4364675 {_104717 _104718 : Type'} : (term385 _104717 _104718) = (term385 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4364674 _104717 _104718 f)). Qed.
Lemma lem4364676 {_104717 : Type'} : (@all ((_104717 -> Prop) -> Prop)) = (@all ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4364677 {_104717 _104718 : Type'} : (term386 _104717 _104718) = (term386 _104717 _104718).
Proof. exact (MK_COMB (@lem4364676 _104717) (@lem4364675 _104717 _104718)). Qed.
Lemma lem4364678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364679 {_104717 _104718 : Type'} : (term387 _104717 _104718) = (term387 _104717 _104718).
Proof. exact (MK_COMB (@lem4364678) (@lem4364677 _104717 _104718)). Qed.
Lemma lem4364680 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term416 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4364679 _104717 _104718) (@lem4364624 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364835 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term418 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4364543 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4364680 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364836 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term416 _104717 _104718 _104757 _104758 _104795 _104796) = (term418 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (SYM (@lem4364835 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364838 (p : Prop) : p = (term417 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4364839 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term416 _104717 _104718 _104757 _104758 _104795 _104796) = (term418 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem4364838 (term416 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364840 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term418 _104717 _104718 _104757 _104758 _104795 _104796) = (term416 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (SYM (@lem4364839 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4364841 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : term419 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (h1). Qed.
Lemma lem4364850 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term425 _104717 f t p1) = (term426 _104717 f t p1).
Proof. exact (@lem17045 (f t) (t p1)). Qed.
Lemma lem4364853 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term361 _104717 f t p1) = (term361 _104717 f t p1).
Proof. exact (eq_refl (term361 _104717 f t p1)). Qed.
Lemma lem4364854 {_104717 : Type'} (P : type686 _104717) : (term427 _104717 P) = (term428 _104717 P).
Proof. exact (@lem18394 (_104717 -> Prop) P). Qed.
Lemma lem4364855 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term429 _104717 f p1) = (term430 _104717 f p1).
Proof. exact (@lem4364854 _104717 (term363 _104717 f p1)). Qed.
Lemma lem4364856 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term431 _104717 f p1 t) = (term361 _104717 f t p1).
Proof. exact (eq_refl (term431 _104717 f p1 t)). Qed.
Lemma lem4364857 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364858 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term432 _104717 f p1 t) = (term425 _104717 f t p1).
Proof. exact (MK_COMB (@lem4364857) (@lem4364856 _104717 f t p1)). Qed.
Lemma lem4364859 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term432 _104717 f p1 t) = (term426 _104717 f t p1).
Proof. exact (TRANS (@lem4364858 _104717 f t p1) (@lem4364850 _104717 f t p1)). Qed.
Lemma lem4364860 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term433 _104717 f p1) = (term434 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4364859 _104717 f t p1)). Qed.
Lemma lem4364861 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4364862 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term430 _104717 f p1) = (term435 _104717 f p1).
Proof. exact (MK_COMB (@lem4364861 _104717) (@lem4364860 _104717 f p1)). Qed.
Lemma lem4364863 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term429 _104717 f p1) = (term435 _104717 f p1).
Proof. exact (TRANS (@lem4364855 _104717 f p1) (@lem4364862 _104717 f p1)). Qed.
Lemma lem4364864 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term363 _104717 f p1) = (term363 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4364853 _104717 f t p1)). Qed.
Lemma lem4364865 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4364866 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term364 _104717 f p1) = (term364 _104717 f p1).
Proof. exact (MK_COMB (@lem4364865 _104717) (@lem4364864 _104717 f p1)). Qed.
Lemma lem4364875 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term425 _104718 g t p2) = (term426 _104718 g t p2).
Proof. exact (@lem17045 (g t) (t p2)). Qed.
Lemma lem4364878 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term361 _104718 g t p2) = (term361 _104718 g t p2).
Proof. exact (eq_refl (term361 _104718 g t p2)). Qed.
Lemma lem4364879 {_104718 : Type'} (P : type686 _104718) : (term427 _104718 P) = (term428 _104718 P).
Proof. exact (@lem18394 (_104718 -> Prop) P). Qed.
Lemma lem4364880 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term429 _104718 g p2) = (term430 _104718 g p2).
Proof. exact (@lem4364879 _104718 (term363 _104718 g p2)). Qed.
Lemma lem4364881 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term431 _104718 g p2 t) = (term361 _104718 g t p2).
Proof. exact (eq_refl (term431 _104718 g p2 t)). Qed.
Lemma lem4364882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364883 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term432 _104718 g p2 t) = (term425 _104718 g t p2).
Proof. exact (MK_COMB (@lem4364882) (@lem4364881 _104718 g t p2)). Qed.
Lemma lem4364884 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term432 _104718 g p2 t) = (term426 _104718 g t p2).
Proof. exact (TRANS (@lem4364883 _104718 g t p2) (@lem4364875 _104718 g t p2)). Qed.
Lemma lem4364885 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term433 _104718 g p2) = (term434 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364884 _104718 g t p2)). Qed.
Lemma lem4364886 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4364887 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term430 _104718 g p2) = (term435 _104718 g p2).
Proof. exact (MK_COMB (@lem4364886 _104718) (@lem4364885 _104718 g p2)). Qed.
Lemma lem4364888 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term429 _104718 g p2) = (term435 _104718 g p2).
Proof. exact (TRANS (@lem4364880 _104718 g p2) (@lem4364887 _104718 g p2)). Qed.
Lemma lem4364889 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term363 _104718 g p2) = (term363 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364878 _104718 g t p2)). Qed.
Lemma lem4364890 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4364891 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term364 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (MK_COMB (@lem4364890 _104718) (@lem4364889 _104718 g p2)). Qed.
Lemma lem4364892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4364893 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term436 _104717 f p1) = (term437 _104717 f p1).
Proof. exact (MK_COMB (@lem4364892) (@lem4364863 _104717 f p1)). Qed.
Lemma lem4364894 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term438 _104717 _104718 f p1 g p2) = (term439 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364893 _104717 f p1) (@lem4364888 _104718 g p2)). Qed.
Lemma lem4364895 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term440 _104717 _104718 f p1 g p2) = (term438 _104717 _104718 f p1 g p2).
Proof. exact (@lem17045 (term364 _104717 f p1) (term364 _104718 g p2)). Qed.
Lemma lem4364896 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term440 _104717 _104718 f p1 g p2) = (term439 _104717 _104718 f p1 g p2).
Proof. exact (TRANS (@lem4364895 _104717 _104718 f p1 g p2) (@lem4364894 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4364897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364898 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term366 _104717 f p1) = (term366 _104717 f p1).
Proof. exact (MK_COMB (@lem4364897) (@lem4364866 _104717 f p1)). Qed.
Lemma lem4364899 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term367 _104717 _104718 f p1 g p2) = (term367 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364898 _104717 f p1) (@lem4364891 _104718 g p2)). Qed.
Lemma lem4364908 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term441 _104717 _104718 f s g t) = (term442 _104717 _104718 f s g t).
Proof. exact (@lem17045 (f s) (g t)). Qed.
Lemma lem4364920 {_104717 _104718 : Type'} (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term443 _104717 _104718 s p1 t p2) = (term444 _104717 _104718 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4364924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4364925 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term445 _104717 _104718 f s g t) = (term446 _104717 _104718 f s g t).
Proof. exact (MK_COMB (@lem4364924) (@lem4364908 _104717 _104718 f s g t)). Qed.
Lemma lem4364926 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term447 _104717 _104718 f g s p1 t p2) = (term448 _104717 _104718 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4364925 _104717 _104718 f s g t) (@lem4364920 _104717 _104718 s p1 t p2)). Qed.
Lemma lem4364927 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term449 _104717 _104718 f g s p1 t p2) = (term447 _104717 _104718 f g s p1 t p2).
Proof. exact (@lem17045 (term369 _104717 _104718 f s g t) (term373 _104717 _104718 s p1 t p2)). Qed.
Lemma lem4364928 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term449 _104717 _104718 f g s p1 t p2) = (term448 _104717 _104718 f g s p1 t p2).
Proof. exact (TRANS (@lem4364927 _104717 _104718 f g s p1 t p2) (@lem4364926 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364931 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term374 _104717 _104718 f g s p1 t p2) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term374 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364932 {_104718 : Type'} (P : type686 _104718) : (term427 _104718 P) = (term428 _104718 P).
Proof. exact (@lem18394 (_104718 -> Prop) P). Qed.
Lemma lem4364933 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term450 _104717 _104718 f g s p1 p2) = (term451 _104717 _104718 f g s p1 p2).
Proof. exact (@lem4364932 _104718 (term375 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364934 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term452 _104717 _104718 f g s p1 p2 t) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term452 _104717 _104718 f g s p1 p2 t)). Qed.
Lemma lem4364935 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364936 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term453 _104717 _104718 f g s p1 p2 t) = (term449 _104717 _104718 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4364935) (@lem4364934 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364937 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term453 _104717 _104718 f g s p1 p2 t) = (term448 _104717 _104718 f g s p1 t p2).
Proof. exact (TRANS (@lem4364936 _104717 _104718 f g s p1 t p2) (@lem4364928 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364938 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term454 _104717 _104718 f g s p1 p2) = (term455 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364937 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364939 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4364940 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term451 _104717 _104718 f g s p1 p2) = (term456 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4364939 _104718) (@lem4364938 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364941 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term450 _104717 _104718 f g s p1 p2) = (term456 _104717 _104718 f g s p1 p2).
Proof. exact (TRANS (@lem4364933 _104717 _104718 f g s p1 p2) (@lem4364940 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364942 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term375 _104717 _104718 f g s p1 p2) = (term375 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4364931 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4364943 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4364944 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term376 _104717 _104718 f g s p1 p2) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4364943 _104718) (@lem4364942 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364945 {_104717 : Type'} (P : type686 _104717) : (term427 _104717 P) = (term428 _104717 P).
Proof. exact (@lem18394 (_104717 -> Prop) P). Qed.
Lemma lem4364946 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term457 _104717 _104718 f g p1 p2) = (term458 _104717 _104718 f g p1 p2).
Proof. exact (@lem4364945 _104717 (term377 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364947 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term459 _104717 _104718 f g p1 p2 s) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (eq_refl (term459 _104717 _104718 f g p1 p2 s)). Qed.
Lemma lem4364948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364949 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term460 _104717 _104718 f g p1 p2 s) = (term450 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4364948) (@lem4364947 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364950 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term460 _104717 _104718 f g p1 p2 s) = (term456 _104717 _104718 f g s p1 p2).
Proof. exact (TRANS (@lem4364949 _104717 _104718 f g s p1 p2) (@lem4364941 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364951 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term461 _104717 _104718 f g p1 p2) = (term462 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4364950 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364952 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4364953 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term458 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364952 _104717) (@lem4364951 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364954 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term457 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4364946 _104717 _104718 f g p1 p2) (@lem4364953 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364955 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term377 _104717 _104718 f g p1 p2) = (term377 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4364944 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4364956 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4364957 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term378 _104717 _104718 f g p1 p2) = (term378 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364956 _104717) (@lem4364955 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364959 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term464 _104717 _104718 f p1 g p2) = (term465 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364958) (@lem4364896 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4364960 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term466 _104717 _104718 f g p1 p2) = (term467 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364959 _104717 _104718 f p1 g p2) (@lem4364957 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4364962 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term468 _104717 _104718 f p1 g p2) = (term468 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4364961) (@lem4364899 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4364963 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term469 _104717 _104718 f g p1 p2) = (term470 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364962 _104717 _104718 f p1 g p2) (@lem4364954 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4364965 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term471 _104717 _104718 f g p1 p2) = (term472 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364964) (@lem4364963 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364966 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term473 _104717 _104718 f g p1 p2) = (term474 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364965 _104717 _104718 f g p1 p2) (@lem4364960 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364967 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term475 _104717 _104718 f g p1 p2) = (term473 _104717 _104718 f g p1 p2).
Proof. exact (@lem17646 (term367 _104717 _104718 f p1 g p2) (term378 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364968 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term475 _104717 _104718 f g p1 p2) = (term474 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4364967 _104717 _104718 f g p1 p2) (@lem4364966 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364969 {_104718 : Type'} (P : _104718 -> Prop) : (term476 _104718 P) = (term477 _104718 P).
Proof. exact (@lem18392 _104718 P). Qed.
Lemma lem4364970 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term478 _104717 _104718 f g p1) = (term479 _104717 _104718 f g p1).
Proof. exact (@lem4364969 _104718 (term379 _104717 _104718 f g p1)). Qed.
Lemma lem4364971 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term480 _104717 _104718 f g p1 p2) = ((term367 _104717 _104718 f p1 g p2) = (term378 _104717 _104718 f g p1 p2)).
Proof. exact (eq_refl (term480 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364973 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term481 _104717 _104718 f g p1 p2) = (term475 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4364972) (@lem4364971 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364974 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term481 _104717 _104718 f g p1 p2) = (term474 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4364973 _104717 _104718 f g p1 p2) (@lem4364968 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364975 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term482 _104717 _104718 f g p1) = (term483 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4364974 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4364976 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4364977 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term479 _104717 _104718 f g p1) = (term484 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4364976 _104718) (@lem4364975 _104717 _104718 f g p1)). Qed.
Lemma lem4364978 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term478 _104717 _104718 f g p1) = (term484 _104717 _104718 f g p1).
Proof. exact (TRANS (@lem4364970 _104717 _104718 f g p1) (@lem4364977 _104717 _104718 f g p1)). Qed.
Lemma lem4364979 {_104717 : Type'} (P : _104717 -> Prop) : (term476 _104717 P) = (term477 _104717 P).
Proof. exact (@lem18392 _104717 P). Qed.
Lemma lem4364980 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term485 _104717 _104718 f g) = (term486 _104717 _104718 f g).
Proof. exact (@lem4364979 _104717 (term381 _104717 _104718 f g)). Qed.
Lemma lem4364981 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term487 _104717 _104718 f g p1) = (term380 _104717 _104718 f g p1).
Proof. exact (eq_refl (term487 _104717 _104718 f g p1)). Qed.
Lemma lem4364982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364983 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term488 _104717 _104718 f g p1) = (term478 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4364982) (@lem4364981 _104717 _104718 f g p1)). Qed.
Lemma lem4364984 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term488 _104717 _104718 f g p1) = (term484 _104717 _104718 f g p1).
Proof. exact (TRANS (@lem4364983 _104717 _104718 f g p1) (@lem4364978 _104717 _104718 f g p1)). Qed.
Lemma lem4364985 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term489 _104717 _104718 f g) = (term490 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4364984 _104717 _104718 f g p1)). Qed.
Lemma lem4364986 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4364987 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term486 _104717 _104718 f g) = (term491 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4364986 _104717) (@lem4364985 _104717 _104718 f g)). Qed.
Lemma lem4364988 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term485 _104717 _104718 f g) = (term491 _104717 _104718 f g).
Proof. exact (TRANS (@lem4364980 _104717 _104718 f g) (@lem4364987 _104717 _104718 f g)). Qed.
Lemma lem4364989 {_104718 : Type'} (P : type180 _104718) : (term492 _104718 P) = (term493 _104718 P).
Proof. exact (@lem18392 (type686 _104718) P). Qed.
Lemma lem4364990 {_104717 _104718 : Type'} (f : type686 _104717) : (term494 _104717 _104718 f) = (term495 _104717 _104718 f).
Proof. exact (@lem4364989 _104718 (term383 _104717 _104718 f)). Qed.
Lemma lem4364991 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term496 _104717 _104718 f g) = (term382 _104717 _104718 f g).
Proof. exact (eq_refl (term496 _104717 _104718 f g)). Qed.
Lemma lem4364992 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4364993 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term497 _104717 _104718 f g) = (term485 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4364992) (@lem4364991 _104717 _104718 f g)). Qed.
Lemma lem4364994 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term497 _104717 _104718 f g) = (term491 _104717 _104718 f g).
Proof. exact (TRANS (@lem4364993 _104717 _104718 f g) (@lem4364988 _104717 _104718 f g)). Qed.
Lemma lem4364995 {_104717 _104718 : Type'} (f : type686 _104717) : (term498 _104717 _104718 f) = (term499 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4364994 _104717 _104718 f g)). Qed.
Lemma lem4364996 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4364997 {_104717 _104718 : Type'} (f : type686 _104717) : (term495 _104717 _104718 f) = (term500 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4364996 _104718) (@lem4364995 _104717 _104718 f)). Qed.
Lemma lem4364998 {_104717 _104718 : Type'} (f : type686 _104717) : (term494 _104717 _104718 f) = (term500 _104717 _104718 f).
Proof. exact (TRANS (@lem4364990 _104717 _104718 f) (@lem4364997 _104717 _104718 f)). Qed.
Lemma lem4364999 {_104717 : Type'} (P : type180 _104717) : (term492 _104717 P) = (term493 _104717 P).
Proof. exact (@lem18392 (type686 _104717) P). Qed.
Lemma lem4365000 {_104717 _104718 : Type'} : (term501 _104717 _104718) = (term502 _104717 _104718).
Proof. exact (@lem4364999 _104717 (term385 _104717 _104718)). Qed.
Lemma lem4365001 {_104717 _104718 : Type'} (f : type686 _104717) : (term503 _104717 _104718 f) = (term384 _104717 _104718 f).
Proof. exact (eq_refl (term503 _104717 _104718 f)). Qed.
Lemma lem4365002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365003 {_104717 _104718 : Type'} (f : type686 _104717) : (term504 _104717 _104718 f) = (term494 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4365002) (@lem4365001 _104717 _104718 f)). Qed.
Lemma lem4365004 {_104717 _104718 : Type'} (f : type686 _104717) : (term504 _104717 _104718 f) = (term500 _104717 _104718 f).
Proof. exact (TRANS (@lem4365003 _104717 _104718 f) (@lem4364998 _104717 _104718 f)). Qed.
Lemma lem4365005 {_104717 _104718 : Type'} : (term505 _104717 _104718) = (term506 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4365004 _104717 _104718 f)). Qed.
Lemma lem4365006 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4365007 {_104717 _104718 : Type'} : (term502 _104717 _104718) = (term507 _104717 _104718).
Proof. exact (MK_COMB (@lem4365006 _104717) (@lem4365005 _104717 _104718)). Qed.
Lemma lem4365008 {_104717 _104718 : Type'} : (term501 _104717 _104718) = (term507 _104717 _104718).
Proof. exact (TRANS (@lem4365000 _104717 _104718) (@lem4365007 _104717 _104718)). Qed.
Lemma lem4365019 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term425 _104758 f t p2) = (term426 _104758 f t p2).
Proof. exact (@lem17045 (f t) (t p2)). Qed.
Lemma lem4365022 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term361 _104758 f t p2) = (term361 _104758 f t p2).
Proof. exact (eq_refl (term361 _104758 f t p2)). Qed.
Lemma lem4365023 {_104758 : Type'} (P : type686 _104758) : (term427 _104758 P) = (term428 _104758 P).
Proof. exact (@lem18394 (_104758 -> Prop) P). Qed.
Lemma lem4365024 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term429 _104758 f p2) = (term430 _104758 f p2).
Proof. exact (@lem4365023 _104758 (term363 _104758 f p2)). Qed.
Lemma lem4365025 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term431 _104758 f p2 t) = (term361 _104758 f t p2).
Proof. exact (eq_refl (term431 _104758 f p2 t)). Qed.
Lemma lem4365026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365027 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term432 _104758 f p2 t) = (term425 _104758 f t p2).
Proof. exact (MK_COMB (@lem4365026) (@lem4365025 _104758 f t p2)). Qed.
Lemma lem4365028 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term432 _104758 f p2 t) = (term426 _104758 f t p2).
Proof. exact (TRANS (@lem4365027 _104758 f t p2) (@lem4365019 _104758 f t p2)). Qed.
Lemma lem4365029 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term433 _104758 f p2) = (term434 _104758 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4365028 _104758 f t p2)). Qed.
Lemma lem4365030 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4365031 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term430 _104758 f p2) = (term435 _104758 f p2).
Proof. exact (MK_COMB (@lem4365030 _104758) (@lem4365029 _104758 f p2)). Qed.
Lemma lem4365032 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term429 _104758 f p2) = (term435 _104758 f p2).
Proof. exact (TRANS (@lem4365024 _104758 f p2) (@lem4365031 _104758 f p2)). Qed.
Lemma lem4365033 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term363 _104758 f p2) = (term363 _104758 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4365022 _104758 f t p2)). Qed.
Lemma lem4365034 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4365035 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term364 _104758 f p2) = (term364 _104758 f p2).
Proof. exact (MK_COMB (@lem4365034 _104758) (@lem4365033 _104758 f p2)). Qed.
Lemma lem4365037 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term508 _104757 s p1) = (term508 _104757 s p1).
Proof. exact (eq_refl (term508 _104757 s p1)). Qed.
Lemma lem4365038 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term509 _104757 _104758 s p1 f p2) = (term510 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4365037 _104757 s p1) (@lem4365032 _104758 f p2)). Qed.
Lemma lem4365039 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term511 _104757 _104758 s p1 f p2) = (term509 _104757 _104758 s p1 f p2).
Proof. exact (@lem17045 (s p1) (term364 _104758 f p2)). Qed.
Lemma lem4365040 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term511 _104757 _104758 s p1 f p2) = (term510 _104757 _104758 s p1 f p2).
Proof. exact (TRANS (@lem4365039 _104757 _104758 s p1 f p2) (@lem4365038 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4365042 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term372 _104757 s p1) = (term372 _104757 s p1).
Proof. exact (eq_refl (term372 _104757 s p1)). Qed.
Lemma lem4365043 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term388 _104757 _104758 s p1 f p2) = (term388 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4365042 _104757 s p1) (@lem4365035 _104758 f p2)). Qed.
Lemma lem4365054 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term443 _104757 _104758 s p1 t p2) = (term444 _104757 _104758 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4365059 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) : (term512 _104758 f t) = (term512 _104758 f t).
Proof. exact (eq_refl (term512 _104758 f t)). Qed.
Lemma lem4365060 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term513 _104757 _104758 f s p1 t p2) = (term514 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4365059 _104758 f t) (@lem4365054 _104757 _104758 s p1 t p2)). Qed.
Lemma lem4365061 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term515 _104757 _104758 f s p1 t p2) = (term513 _104757 _104758 f s p1 t p2).
Proof. exact (@lem17045 (f t) (term373 _104757 _104758 s p1 t p2)). Qed.
Lemma lem4365062 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term515 _104757 _104758 f s p1 t p2) = (term514 _104757 _104758 f s p1 t p2).
Proof. exact (TRANS (@lem4365061 _104757 _104758 f s p1 t p2) (@lem4365060 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365065 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term390 _104757 _104758 f s p1 t p2) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term390 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365066 {_104758 : Type'} (P : type686 _104758) : (term427 _104758 P) = (term428 _104758 P).
Proof. exact (@lem18394 (_104758 -> Prop) P). Qed.
Lemma lem4365067 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term516 _104757 _104758 f s p1 p2) = (term517 _104757 _104758 f s p1 p2).
Proof. exact (@lem4365066 _104758 (term391 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365068 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term518 _104757 _104758 f s p1 p2 t) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term518 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4365069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365070 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term519 _104757 _104758 f s p1 p2 t) = (term515 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4365069) (@lem4365068 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365071 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term519 _104757 _104758 f s p1 p2 t) = (term514 _104757 _104758 f s p1 t p2).
Proof. exact (TRANS (@lem4365070 _104757 _104758 f s p1 t p2) (@lem4365062 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365072 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term520 _104757 _104758 f s p1 p2) = (term521 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4365071 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365073 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4365074 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term517 _104757 _104758 f s p1 p2) = (term522 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365073 _104758) (@lem4365072 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365075 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term516 _104757 _104758 f s p1 p2) = (term522 _104757 _104758 f s p1 p2).
Proof. exact (TRANS (@lem4365067 _104757 _104758 f s p1 p2) (@lem4365074 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365076 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term391 _104757 _104758 f s p1 p2) = (term391 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4365065 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4365077 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4365078 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term392 _104757 _104758 f s p1 p2) = (term392 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365077 _104758) (@lem4365076 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4365080 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term523 _104757 _104758 s p1 f p2) = (term524 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4365079) (@lem4365040 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4365081 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term525 _104757 _104758 f s p1 p2) = (term526 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365080 _104757 _104758 s p1 f p2) (@lem4365078 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4365083 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term527 _104757 _104758 s p1 f p2) = (term527 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4365082) (@lem4365043 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4365084 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term528 _104757 _104758 f s p1 p2) = (term529 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365083 _104757 _104758 s p1 f p2) (@lem4365075 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365086 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term530 _104757 _104758 f s p1 p2) = (term531 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365085) (@lem4365084 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365087 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term532 _104757 _104758 f s p1 p2) = (term533 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365086 _104757 _104758 f s p1 p2) (@lem4365081 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365088 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term534 _104757 _104758 f s p1 p2) = (term532 _104757 _104758 f s p1 p2).
Proof. exact (@lem17646 (term388 _104757 _104758 s p1 f p2) (term392 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365089 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term534 _104757 _104758 f s p1 p2) = (term533 _104757 _104758 f s p1 p2).
Proof. exact (TRANS (@lem4365088 _104757 _104758 f s p1 p2) (@lem4365087 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365090 {_104758 : Type'} (P : _104758 -> Prop) : (term476 _104758 P) = (term477 _104758 P).
Proof. exact (@lem18392 _104758 P). Qed.
Lemma lem4365091 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term535 _104757 _104758 f s p1) = (term536 _104757 _104758 f s p1).
Proof. exact (@lem4365090 _104758 (term393 _104757 _104758 f s p1)). Qed.
Lemma lem4365092 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term537 _104757 _104758 f s p1 p2) = ((term388 _104757 _104758 s p1 f p2) = (term392 _104757 _104758 f s p1 p2)).
Proof. exact (eq_refl (term537 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365094 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term538 _104757 _104758 f s p1 p2) = (term534 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4365093) (@lem4365092 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365095 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term538 _104757 _104758 f s p1 p2) = (term533 _104757 _104758 f s p1 p2).
Proof. exact (TRANS (@lem4365094 _104757 _104758 f s p1 p2) (@lem4365089 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365096 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term539 _104757 _104758 f s p1) = (term540 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4365095 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4365097 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4365098 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term536 _104757 _104758 f s p1) = (term541 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4365097 _104758) (@lem4365096 _104757 _104758 f s p1)). Qed.
Lemma lem4365099 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term535 _104757 _104758 f s p1) = (term541 _104757 _104758 f s p1).
Proof. exact (TRANS (@lem4365091 _104757 _104758 f s p1) (@lem4365098 _104757 _104758 f s p1)). Qed.
Lemma lem4365100 {_104757 : Type'} (P : _104757 -> Prop) : (term476 _104757 P) = (term477 _104757 P).
Proof. exact (@lem18392 _104757 P). Qed.
Lemma lem4365101 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term542 _104757 _104758 f s) = (term543 _104757 _104758 f s).
Proof. exact (@lem4365100 _104757 (term395 _104757 _104758 f s)). Qed.
Lemma lem4365102 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term544 _104757 _104758 f s p1) = (term394 _104757 _104758 f s p1).
Proof. exact (eq_refl (term544 _104757 _104758 f s p1)). Qed.
Lemma lem4365103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365104 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term545 _104757 _104758 f s p1) = (term535 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4365103) (@lem4365102 _104757 _104758 f s p1)). Qed.
Lemma lem4365105 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term545 _104757 _104758 f s p1) = (term541 _104757 _104758 f s p1).
Proof. exact (TRANS (@lem4365104 _104757 _104758 f s p1) (@lem4365099 _104757 _104758 f s p1)). Qed.
Lemma lem4365106 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term546 _104757 _104758 f s) = (term547 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4365105 _104757 _104758 f s p1)). Qed.
Lemma lem4365107 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4365108 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term543 _104757 _104758 f s) = (term548 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4365107 _104757) (@lem4365106 _104757 _104758 f s)). Qed.
Lemma lem4365109 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term542 _104757 _104758 f s) = (term548 _104757 _104758 f s).
Proof. exact (TRANS (@lem4365101 _104757 _104758 f s) (@lem4365108 _104757 _104758 f s)). Qed.
Lemma lem4365110 {_104758 : Type'} (P : type180 _104758) : (term492 _104758 P) = (term493 _104758 P).
Proof. exact (@lem18392 (type686 _104758) P). Qed.
Lemma lem4365111 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term549 _104757 _104758 s) = (term550 _104757 _104758 s).
Proof. exact (@lem4365110 _104758 (term397 _104757 _104758 s)). Qed.
Lemma lem4365112 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term551 _104757 _104758 s f) = (term396 _104757 _104758 f s).
Proof. exact (eq_refl (term551 _104757 _104758 s f)). Qed.
Lemma lem4365113 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365114 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term552 _104757 _104758 s f) = (term542 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4365113) (@lem4365112 _104757 _104758 f s)). Qed.
Lemma lem4365115 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term552 _104757 _104758 s f) = (term548 _104757 _104758 f s).
Proof. exact (TRANS (@lem4365114 _104757 _104758 f s) (@lem4365109 _104757 _104758 f s)). Qed.
Lemma lem4365116 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term553 _104757 _104758 s) = (term554 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4365115 _104757 _104758 f s)). Qed.
Lemma lem4365117 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4365118 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term550 _104757 _104758 s) = (term555 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4365117 _104758) (@lem4365116 _104757 _104758 s)). Qed.
Lemma lem4365119 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term549 _104757 _104758 s) = (term555 _104757 _104758 s).
Proof. exact (TRANS (@lem4365111 _104757 _104758 s) (@lem4365118 _104757 _104758 s)). Qed.
Lemma lem4365120 {_104757 : Type'} (P : type686 _104757) : (term556 _104757 P) = (term557 _104757 P).
Proof. exact (@lem18392 (_104757 -> Prop) P). Qed.
Lemma lem4365121 {_104757 _104758 : Type'} : (term558 _104757 _104758) = (term559 _104757 _104758).
Proof. exact (@lem4365120 _104757 (term399 _104757 _104758)). Qed.
Lemma lem4365122 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term560 _104757 _104758 s) = (term398 _104757 _104758 s).
Proof. exact (eq_refl (term560 _104757 _104758 s)). Qed.
Lemma lem4365123 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365124 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term561 _104757 _104758 s) = (term549 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4365123) (@lem4365122 _104757 _104758 s)). Qed.
Lemma lem4365125 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term561 _104757 _104758 s) = (term555 _104757 _104758 s).
Proof. exact (TRANS (@lem4365124 _104757 _104758 s) (@lem4365119 _104757 _104758 s)). Qed.
Lemma lem4365126 {_104757 _104758 : Type'} : (term562 _104757 _104758) = (term563 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4365125 _104757 _104758 s)). Qed.
Lemma lem4365127 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4365128 {_104757 _104758 : Type'} : (term559 _104757 _104758) = (term564 _104757 _104758).
Proof. exact (MK_COMB (@lem4365127 _104757) (@lem4365126 _104757 _104758)). Qed.
Lemma lem4365129 {_104757 _104758 : Type'} : (term558 _104757 _104758) = (term564 _104757 _104758).
Proof. exact (TRANS (@lem4365121 _104757 _104758) (@lem4365128 _104757 _104758)). Qed.
Lemma lem4365138 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term425 _104795 f t p1) = (term426 _104795 f t p1).
Proof. exact (@lem17045 (f t) (t p1)). Qed.
Lemma lem4365141 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term361 _104795 f t p1) = (term361 _104795 f t p1).
Proof. exact (eq_refl (term361 _104795 f t p1)). Qed.
Lemma lem4365142 {_104795 : Type'} (P : type686 _104795) : (term427 _104795 P) = (term428 _104795 P).
Proof. exact (@lem18394 (_104795 -> Prop) P). Qed.
Lemma lem4365143 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term429 _104795 f p1) = (term430 _104795 f p1).
Proof. exact (@lem4365142 _104795 (term363 _104795 f p1)). Qed.
Lemma lem4365144 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term431 _104795 f p1 t) = (term361 _104795 f t p1).
Proof. exact (eq_refl (term431 _104795 f p1 t)). Qed.
Lemma lem4365145 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365146 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term432 _104795 f p1 t) = (term425 _104795 f t p1).
Proof. exact (MK_COMB (@lem4365145) (@lem4365144 _104795 f t p1)). Qed.
Lemma lem4365147 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term432 _104795 f p1 t) = (term426 _104795 f t p1).
Proof. exact (TRANS (@lem4365146 _104795 f t p1) (@lem4365138 _104795 f t p1)). Qed.
Lemma lem4365148 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term433 _104795 f p1) = (term434 _104795 f p1).
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4365147 _104795 f t p1)). Qed.
Lemma lem4365149 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4365150 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term430 _104795 f p1) = (term435 _104795 f p1).
Proof. exact (MK_COMB (@lem4365149 _104795) (@lem4365148 _104795 f p1)). Qed.
Lemma lem4365151 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term429 _104795 f p1) = (term435 _104795 f p1).
Proof. exact (TRANS (@lem4365143 _104795 f p1) (@lem4365150 _104795 f p1)). Qed.
Lemma lem4365152 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term363 _104795 f p1) = (term363 _104795 f p1).
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4365141 _104795 f t p1)). Qed.
Lemma lem4365153 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4365154 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term364 _104795 f p1) = (term364 _104795 f p1).
Proof. exact (MK_COMB (@lem4365153 _104795) (@lem4365152 _104795 f p1)). Qed.
Lemma lem4365155 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (term565 _104796 t p2) = (term565 _104796 t p2).
Proof. exact (eq_refl (term565 _104796 t p2)). Qed.
Lemma lem4365156 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4365157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365158 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term436 _104795 f p1) = (term437 _104795 f p1).
Proof. exact (MK_COMB (@lem4365157) (@lem4365151 _104795 f p1)). Qed.
Lemma lem4365159 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term566 _104795 _104796 f p1 t p2) = (term567 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365158 _104795 f p1) (@lem4365155 _104796 t p2)). Qed.
Lemma lem4365160 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term568 _104795 _104796 f p1 t p2) = (term566 _104795 _104796 f p1 t p2).
Proof. exact (@lem17045 (term364 _104795 f p1) (t p2)). Qed.
Lemma lem4365161 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term568 _104795 _104796 f p1 t p2) = (term567 _104795 _104796 f p1 t p2).
Proof. exact (TRANS (@lem4365160 _104795 _104796 f p1 t p2) (@lem4365159 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4365163 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term366 _104795 f p1) = (term366 _104795 f p1).
Proof. exact (MK_COMB (@lem4365162) (@lem4365154 _104795 f p1)). Qed.
Lemma lem4365164 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term402 _104795 _104796 f p1 t p2) = (term402 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365163 _104795 f p1) (@lem4365156 _104796 t p2)). Qed.
Lemma lem4365175 {_104795 _104796 : Type'} (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term443 _104795 _104796 s p1 t p2) = (term444 _104795 _104796 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4365180 {_104795 : Type'} (f : type686 _104795) (s : _104795 -> Prop) : (term512 _104795 f s) = (term512 _104795 f s).
Proof. exact (eq_refl (term512 _104795 f s)). Qed.
Lemma lem4365181 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term569 _104795 _104796 f s p1 t p2) = (term570 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4365180 _104795 f s) (@lem4365175 _104795 _104796 s p1 t p2)). Qed.
Lemma lem4365182 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term571 _104795 _104796 f s p1 t p2) = (term569 _104795 _104796 f s p1 t p2).
Proof. exact (@lem17045 (f s) (term373 _104795 _104796 s p1 t p2)). Qed.
Lemma lem4365183 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term571 _104795 _104796 f s p1 t p2) = (term570 _104795 _104796 f s p1 t p2).
Proof. exact (TRANS (@lem4365182 _104795 _104796 f s p1 t p2) (@lem4365181 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365186 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term404 _104795 _104796 f s p1 t p2) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term404 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365187 {_104795 : Type'} (P : type686 _104795) : (term427 _104795 P) = (term428 _104795 P).
Proof. exact (@lem18394 (_104795 -> Prop) P). Qed.
Lemma lem4365188 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term572 _104795 _104796 f p1 t p2) = (term573 _104795 _104796 f p1 t p2).
Proof. exact (@lem4365187 _104795 (term405 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365189 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term574 _104795 _104796 f p1 t p2 s) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term574 _104795 _104796 f p1 t p2 s)). Qed.
Lemma lem4365190 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365191 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term575 _104795 _104796 f p1 t p2 s) = (term571 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4365190) (@lem4365189 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365192 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term575 _104795 _104796 f p1 t p2 s) = (term570 _104795 _104796 f s p1 t p2).
Proof. exact (TRANS (@lem4365191 _104795 _104796 f s p1 t p2) (@lem4365183 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365193 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term576 _104795 _104796 f p1 t p2) = (term577 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4365192 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365194 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4365195 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term573 _104795 _104796 f p1 t p2) = (term578 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365194 _104795) (@lem4365193 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365196 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term572 _104795 _104796 f p1 t p2) = (term578 _104795 _104796 f p1 t p2).
Proof. exact (TRANS (@lem4365188 _104795 _104796 f p1 t p2) (@lem4365195 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365197 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term405 _104795 _104796 f p1 t p2) = (term405 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4365186 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4365198 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4365199 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term406 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365198 _104795) (@lem4365197 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4365201 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term579 _104795 _104796 f p1 t p2) = (term580 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365200) (@lem4365161 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365202 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term581 _104795 _104796 f p1 t p2) = (term582 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365201 _104795 _104796 f p1 t p2) (@lem4365199 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4365204 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term583 _104795 _104796 f p1 t p2) = (term583 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365203) (@lem4365164 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365205 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term584 _104795 _104796 f p1 t p2) = (term585 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365204 _104795 _104796 f p1 t p2) (@lem4365196 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365207 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term586 _104795 _104796 f p1 t p2) = (term587 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365206) (@lem4365205 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365208 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term588 _104795 _104796 f p1 t p2) = (term589 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365207 _104795 _104796 f p1 t p2) (@lem4365202 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365209 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term590 _104795 _104796 f p1 t p2) = (term588 _104795 _104796 f p1 t p2).
Proof. exact (@lem17646 (term402 _104795 _104796 f p1 t p2) (term406 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365210 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term590 _104795 _104796 f p1 t p2) = (term589 _104795 _104796 f p1 t p2).
Proof. exact (TRANS (@lem4365209 _104795 _104796 f p1 t p2) (@lem4365208 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365211 {_104796 : Type'} (P : _104796 -> Prop) : (term476 _104796 P) = (term477 _104796 P).
Proof. exact (@lem18392 _104796 P). Qed.
Lemma lem4365212 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term591 _104795 _104796 f p1 t) = (term592 _104795 _104796 f p1 t).
Proof. exact (@lem4365211 _104796 (term407 _104795 _104796 f p1 t)). Qed.
Lemma lem4365213 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term593 _104795 _104796 f p1 t p2) = ((term402 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2)).
Proof. exact (eq_refl (term593 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365215 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term594 _104795 _104796 f p1 t p2) = (term590 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4365214) (@lem4365213 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365216 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term594 _104795 _104796 f p1 t p2) = (term589 _104795 _104796 f p1 t p2).
Proof. exact (TRANS (@lem4365215 _104795 _104796 f p1 t p2) (@lem4365210 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365217 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term595 _104795 _104796 f p1 t) = (term596 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4365216 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4365218 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4365219 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term592 _104795 _104796 f p1 t) = (term597 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4365218 _104796) (@lem4365217 _104795 _104796 f p1 t)). Qed.
Lemma lem4365220 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term591 _104795 _104796 f p1 t) = (term597 _104795 _104796 f p1 t).
Proof. exact (TRANS (@lem4365212 _104795 _104796 f p1 t) (@lem4365219 _104795 _104796 f p1 t)). Qed.
Lemma lem4365221 {_104795 : Type'} (P : _104795 -> Prop) : (term476 _104795 P) = (term477 _104795 P).
Proof. exact (@lem18392 _104795 P). Qed.
Lemma lem4365222 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term598 _104795 _104796 f t) = (term599 _104795 _104796 f t).
Proof. exact (@lem4365221 _104795 (term409 _104795 _104796 f t)). Qed.
Lemma lem4365223 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term600 _104795 _104796 f t p1) = (term408 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term600 _104795 _104796 f t p1)). Qed.
Lemma lem4365224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365225 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term601 _104795 _104796 f t p1) = (term591 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4365224) (@lem4365223 _104795 _104796 f p1 t)). Qed.
Lemma lem4365226 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term601 _104795 _104796 f t p1) = (term597 _104795 _104796 f p1 t).
Proof. exact (TRANS (@lem4365225 _104795 _104796 f p1 t) (@lem4365220 _104795 _104796 f p1 t)). Qed.
Lemma lem4365227 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term602 _104795 _104796 f t) = (term603 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4365226 _104795 _104796 f p1 t)). Qed.
Lemma lem4365228 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4365229 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term599 _104795 _104796 f t) = (term604 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4365228 _104795) (@lem4365227 _104795 _104796 f t)). Qed.
Lemma lem4365230 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term598 _104795 _104796 f t) = (term604 _104795 _104796 f t).
Proof. exact (TRANS (@lem4365222 _104795 _104796 f t) (@lem4365229 _104795 _104796 f t)). Qed.
Lemma lem4365231 {_104796 : Type'} (P : type686 _104796) : (term556 _104796 P) = (term557 _104796 P).
Proof. exact (@lem18392 (_104796 -> Prop) P). Qed.
Lemma lem4365232 {_104795 _104796 : Type'} (f : type686 _104795) : (term605 _104795 _104796 f) = (term606 _104795 _104796 f).
Proof. exact (@lem4365231 _104796 (term411 _104795 _104796 f)). Qed.
Lemma lem4365233 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term607 _104795 _104796 f t) = (term410 _104795 _104796 f t).
Proof. exact (eq_refl (term607 _104795 _104796 f t)). Qed.
Lemma lem4365234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365235 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term608 _104795 _104796 f t) = (term598 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4365234) (@lem4365233 _104795 _104796 f t)). Qed.
Lemma lem4365236 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term608 _104795 _104796 f t) = (term604 _104795 _104796 f t).
Proof. exact (TRANS (@lem4365235 _104795 _104796 f t) (@lem4365230 _104795 _104796 f t)). Qed.
Lemma lem4365237 {_104795 _104796 : Type'} (f : type686 _104795) : (term609 _104795 _104796 f) = (term610 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4365236 _104795 _104796 f t)). Qed.
Lemma lem4365238 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4365239 {_104795 _104796 : Type'} (f : type686 _104795) : (term606 _104795 _104796 f) = (term611 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4365238 _104796) (@lem4365237 _104795 _104796 f)). Qed.
Lemma lem4365240 {_104795 _104796 : Type'} (f : type686 _104795) : (term605 _104795 _104796 f) = (term611 _104795 _104796 f).
Proof. exact (TRANS (@lem4365232 _104795 _104796 f) (@lem4365239 _104795 _104796 f)). Qed.
Lemma lem4365241 {_104795 : Type'} (P : type180 _104795) : (term492 _104795 P) = (term493 _104795 P).
Proof. exact (@lem18392 (type686 _104795) P). Qed.
Lemma lem4365242 {_104795 _104796 : Type'} : (term612 _104795 _104796) = (term613 _104795 _104796).
Proof. exact (@lem4365241 _104795 (term413 _104795 _104796)). Qed.
Lemma lem4365243 {_104795 _104796 : Type'} (f : type686 _104795) : (term614 _104795 _104796 f) = (term412 _104795 _104796 f).
Proof. exact (eq_refl (term614 _104795 _104796 f)). Qed.
Lemma lem4365244 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4365245 {_104795 _104796 : Type'} (f : type686 _104795) : (term615 _104795 _104796 f) = (term605 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4365244) (@lem4365243 _104795 _104796 f)). Qed.
Lemma lem4365246 {_104795 _104796 : Type'} (f : type686 _104795) : (term615 _104795 _104796 f) = (term611 _104795 _104796 f).
Proof. exact (TRANS (@lem4365245 _104795 _104796 f) (@lem4365240 _104795 _104796 f)). Qed.
Lemma lem4365247 {_104795 _104796 : Type'} : (term616 _104795 _104796) = (term617 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4365246 _104795 _104796 f)). Qed.
Lemma lem4365248 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4365249 {_104795 _104796 : Type'} : (term613 _104795 _104796) = (term618 _104795 _104796).
Proof. exact (MK_COMB (@lem4365248 _104795) (@lem4365247 _104795 _104796)). Qed.
Lemma lem4365250 {_104795 _104796 : Type'} : (term612 _104795 _104796) = (term618 _104795 _104796).
Proof. exact (TRANS (@lem4365242 _104795 _104796) (@lem4365249 _104795 _104796)). Qed.
Lemma lem4365251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365252 {_104757 _104758 : Type'} : (term619 _104757 _104758) = (term620 _104757 _104758).
Proof. exact (MK_COMB (@lem4365251) (@lem4365129 _104757 _104758)). Qed.
Lemma lem4365253 {_104757 _104758 _104795 _104796 : Type'} : (term621 _104757 _104758 _104795 _104796) = (term622 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4365252 _104757 _104758) (@lem4365250 _104795 _104796)). Qed.
Lemma lem4365254 {_104757 _104758 _104795 _104796 : Type'} : (term623 _104757 _104758 _104795 _104796) = (term621 _104757 _104758 _104795 _104796).
Proof. exact (@lem17045 (term400 _104757 _104758) (term414 _104795 _104796)). Qed.
Lemma lem4365255 {_104757 _104758 _104795 _104796 : Type'} : (term623 _104757 _104758 _104795 _104796) = (term622 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4365254 _104757 _104758 _104795 _104796) (@lem4365253 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4365256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365257 {_104717 _104718 : Type'} : (term624 _104717 _104718) = (term625 _104717 _104718).
Proof. exact (MK_COMB (@lem4365256) (@lem4365008 _104717 _104718)). Qed.
Lemma lem4365258 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term626 _104717 _104718 _104757 _104758 _104795 _104796) = (term627 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4365257 _104717 _104718) (@lem4365255 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4365259 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term419 _104717 _104718 _104757 _104758 _104795 _104796) = (term626 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem17045 (term386 _104717 _104718) (term415 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4365260 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term419 _104717 _104718 _104757 _104758 _104795 _104796) = (term627 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4365259 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4365258 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4365274 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4365275 {_104718 : Type'} (P : _104718 -> Prop) (Q : _104718 -> Prop) : (term628 _104718 P Q) = (term629 _104718 P Q).
Proof. exact (@lem4365274 _104718 P Q). Qed.
Lemma lem4365276 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term630 _104717 _104718 f g p1) = (term631 _104717 _104718 f g p1).
Proof. exact (@lem4365275 _104718 (term632 _104717 _104718 f g p1) (term633 _104717 _104718 f g p1)). Qed.
Lemma lem4365277 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term634 _104717 _104718 f g p1 p2) = (term470 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term634 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365279 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term635 _104717 _104718 f g p1 p2) = (term472 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4365278) (@lem4365277 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365280 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term636 _104717 _104718 f g p1 p2) = (term467 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term636 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365281 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term637 _104717 _104718 f g p1 p2) = (term474 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4365279 _104717 _104718 f g p1 p2) (@lem4365280 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365282 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term638 _104717 _104718 f g p1) = (term483 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4365281 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365283 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4365284 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term630 _104717 _104718 f g p1) = (term484 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365283 _104718) (@lem4365282 _104717 _104718 f g p1)). Qed.
Lemma lem4365285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4365286 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term639 _104717 _104718 f g p1) = (term640 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365285) (@lem4365284 _104717 _104718 f g p1)). Qed.
Lemma lem4365287 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term634 _104717 _104718 f g p1 p2) = (term470 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term634 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365288 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term641 _104717 _104718 f g p1) = (term632 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4365287 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365289 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4365290 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term642 _104717 _104718 f g p1) = (term643 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365289 _104718) (@lem4365288 _104717 _104718 f g p1)). Qed.
Lemma lem4365291 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365292 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term644 _104717 _104718 f g p1) = (term645 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365291) (@lem4365290 _104717 _104718 f g p1)). Qed.
Lemma lem4365293 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term636 _104717 _104718 f g p1 p2) = (term467 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term636 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365294 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term646 _104717 _104718 f g p1) = (term633 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4365293 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4365295 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4365296 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term647 _104717 _104718 f g p1) = (term648 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365295 _104718) (@lem4365294 _104717 _104718 f g p1)). Qed.
Lemma lem4365297 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term631 _104717 _104718 f g p1) = (term649 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365292 _104717 _104718 f g p1) (@lem4365296 _104717 _104718 f g p1)). Qed.
Lemma lem4365298 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : ((term630 _104717 _104718 f g p1) = (term631 _104717 _104718 f g p1)) = ((term484 _104717 _104718 f g p1) = (term649 _104717 _104718 f g p1)).
Proof. exact (MK_COMB (@lem4365286 _104717 _104718 f g p1) (@lem4365297 _104717 _104718 f g p1)). Qed.
Lemma lem4365299 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term484 _104717 _104718 f g p1) = (term649 _104717 _104718 f g p1).
Proof. exact (EQ_MP (@lem4365298 _104717 _104718 f g p1) (@lem4365276 _104717 _104718 f g p1)). Qed.
Lemma lem4365652 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term490 _104717 _104718 f g) = (term650 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4365299 _104717 _104718 f g p1)). Qed.
Lemma lem4365653 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4365654 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term491 _104717 _104718 f g) = (term651 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365653 _104717) (@lem4365652 _104717 _104718 f g)). Qed.
Lemma lem4365656 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4365657 {_104717 : Type'} (P : _104717 -> Prop) (Q : _104717 -> Prop) : (term628 _104717 P Q) = (term629 _104717 P Q).
Proof. exact (@lem4365656 _104717 P Q). Qed.
Lemma lem4365658 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term652 _104717 _104718 f g) = (term653 _104717 _104718 f g).
Proof. exact (@lem4365657 _104717 (term654 _104717 _104718 f g) (term655 _104717 _104718 f g)). Qed.
Lemma lem4365659 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term656 _104717 _104718 f g p1) = (term643 _104717 _104718 f g p1).
Proof. exact (eq_refl (term656 _104717 _104718 f g p1)). Qed.
Lemma lem4365660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365661 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term657 _104717 _104718 f g p1) = (term645 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365660) (@lem4365659 _104717 _104718 f g p1)). Qed.
Lemma lem4365662 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term658 _104717 _104718 f g p1) = (term648 _104717 _104718 f g p1).
Proof. exact (eq_refl (term658 _104717 _104718 f g p1)). Qed.
Lemma lem4365663 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term659 _104717 _104718 f g p1) = (term649 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4365661 _104717 _104718 f g p1) (@lem4365662 _104717 _104718 f g p1)). Qed.
Lemma lem4365664 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term660 _104717 _104718 f g) = (term650 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4365663 _104717 _104718 f g p1)). Qed.
Lemma lem4365665 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4365666 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term652 _104717 _104718 f g) = (term651 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365665 _104717) (@lem4365664 _104717 _104718 f g)). Qed.
Lemma lem4365667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4365668 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term661 _104717 _104718 f g) = (term662 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365667) (@lem4365666 _104717 _104718 f g)). Qed.
Lemma lem4365669 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term656 _104717 _104718 f g p1) = (term643 _104717 _104718 f g p1).
Proof. exact (eq_refl (term656 _104717 _104718 f g p1)). Qed.
Lemma lem4365670 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term663 _104717 _104718 f g) = (term654 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4365669 _104717 _104718 f g p1)). Qed.
Lemma lem4365671 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4365672 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term664 _104717 _104718 f g) = (term665 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365671 _104717) (@lem4365670 _104717 _104718 f g)). Qed.
Lemma lem4365673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4365674 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term666 _104717 _104718 f g) = (term667 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365673) (@lem4365672 _104717 _104718 f g)). Qed.
Lemma lem4365675 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term658 _104717 _104718 f g p1) = (term648 _104717 _104718 f g p1).
Proof. exact (eq_refl (term658 _104717 _104718 f g p1)). Qed.
Lemma lem4365676 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term668 _104717 _104718 f g) = (term655 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4365675 _104717 _104718 f g p1)). Qed.
Lemma lem4365677 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4365678 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term669 _104717 _104718 f g) = (term670 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365677 _104717) (@lem4365676 _104717 _104718 f g)). Qed.
Lemma lem4365679 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term653 _104717 _104718 f g) = (term671 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4365674 _104717 _104718 f g) (@lem4365678 _104717 _104718 f g)). Qed.
Lemma lem4365680 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term652 _104717 _104718 f g) = (term653 _104717 _104718 f g)) = ((term651 _104717 _104718 f g) = (term671 _104717 _104718 f g)).
Proof. exact (MK_COMB (@lem4365668 _104717 _104718 f g) (@lem4365679 _104717 _104718 f g)). Qed.
Lemma lem4365681 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term651 _104717 _104718 f g) = (term671 _104717 _104718 f g).
Proof. exact (EQ_MP (@lem4365680 _104717 _104718 f g) (@lem4365658 _104717 _104718 f g)). Qed.
Lemma lem4366042 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term491 _104717 _104718 f g) = (term671 _104717 _104718 f g).
Proof. exact (TRANS (@lem4365654 _104717 _104718 f g) (@lem4365681 _104717 _104718 f g)). Qed.
Lemma lem4366043 {_104717 _104718 : Type'} (f : type686 _104717) : (term499 _104717 _104718 f) = (term672 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4366042 _104717 _104718 f g)). Qed.
Lemma lem4366044 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4366045 {_104717 _104718 : Type'} (f : type686 _104717) : (term500 _104717 _104718 f) = (term673 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366044 _104718) (@lem4366043 _104717 _104718 f)). Qed.
Lemma lem4366047 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4366048 {_104718 : Type'} (P : type180 _104718) (Q : type180 _104718) : (term674 _104718 P Q) = (term675 _104718 P Q).
Proof. exact (@lem4366047 (type686 _104718) P Q). Qed.
Lemma lem4366049 {_104717 _104718 : Type'} (f : type686 _104717) : (term676 _104717 _104718 f) = (term677 _104717 _104718 f).
Proof. exact (@lem4366048 _104718 (term678 _104717 _104718 f) (term679 _104717 _104718 f)). Qed.
Lemma lem4366050 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term680 _104717 _104718 f g) = (term665 _104717 _104718 f g).
Proof. exact (eq_refl (term680 _104717 _104718 f g)). Qed.
Lemma lem4366051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366052 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term681 _104717 _104718 f g) = (term667 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4366051) (@lem4366050 _104717 _104718 f g)). Qed.
Lemma lem4366053 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term682 _104717 _104718 f g) = (term670 _104717 _104718 f g).
Proof. exact (eq_refl (term682 _104717 _104718 f g)). Qed.
Lemma lem4366054 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term683 _104717 _104718 f g) = (term671 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4366052 _104717 _104718 f g) (@lem4366053 _104717 _104718 f g)). Qed.
Lemma lem4366055 {_104717 _104718 : Type'} (f : type686 _104717) : (term684 _104717 _104718 f) = (term672 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4366054 _104717 _104718 f g)). Qed.
Lemma lem4366056 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4366057 {_104717 _104718 : Type'} (f : type686 _104717) : (term676 _104717 _104718 f) = (term673 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366056 _104718) (@lem4366055 _104717 _104718 f)). Qed.
Lemma lem4366058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4366059 {_104717 _104718 : Type'} (f : type686 _104717) : (term685 _104717 _104718 f) = (term686 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366058) (@lem4366057 _104717 _104718 f)). Qed.
Lemma lem4366060 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term680 _104717 _104718 f g) = (term665 _104717 _104718 f g).
Proof. exact (eq_refl (term680 _104717 _104718 f g)). Qed.
Lemma lem4366061 {_104717 _104718 : Type'} (f : type686 _104717) : (term687 _104717 _104718 f) = (term678 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4366060 _104717 _104718 f g)). Qed.
Lemma lem4366062 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4366063 {_104717 _104718 : Type'} (f : type686 _104717) : (term688 _104717 _104718 f) = (term689 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366062 _104718) (@lem4366061 _104717 _104718 f)). Qed.
Lemma lem4366064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366065 {_104717 _104718 : Type'} (f : type686 _104717) : (term690 _104717 _104718 f) = (term691 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366064) (@lem4366063 _104717 _104718 f)). Qed.
Lemma lem4366066 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term682 _104717 _104718 f g) = (term670 _104717 _104718 f g).
Proof. exact (eq_refl (term682 _104717 _104718 f g)). Qed.
Lemma lem4366067 {_104717 _104718 : Type'} (f : type686 _104717) : (term692 _104717 _104718 f) = (term679 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4366066 _104717 _104718 f g)). Qed.
Lemma lem4366068 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4366069 {_104717 _104718 : Type'} (f : type686 _104717) : (term693 _104717 _104718 f) = (term694 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366068 _104718) (@lem4366067 _104717 _104718 f)). Qed.
Lemma lem4366070 {_104717 _104718 : Type'} (f : type686 _104717) : (term677 _104717 _104718 f) = (term695 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366065 _104717 _104718 f) (@lem4366069 _104717 _104718 f)). Qed.
Lemma lem4366071 {_104717 _104718 : Type'} (f : type686 _104717) : ((term676 _104717 _104718 f) = (term677 _104717 _104718 f)) = ((term673 _104717 _104718 f) = (term695 _104717 _104718 f)).
Proof. exact (MK_COMB (@lem4366059 _104717 _104718 f) (@lem4366070 _104717 _104718 f)). Qed.
Lemma lem4366072 {_104717 _104718 : Type'} (f : type686 _104717) : (term673 _104717 _104718 f) = (term695 _104717 _104718 f).
Proof. exact (EQ_MP (@lem4366071 _104717 _104718 f) (@lem4366049 _104717 _104718 f)). Qed.
Lemma lem4366441 {_104717 _104718 : Type'} (f : type686 _104717) : (term500 _104717 _104718 f) = (term695 _104717 _104718 f).
Proof. exact (TRANS (@lem4366045 _104717 _104718 f) (@lem4366072 _104717 _104718 f)). Qed.
Lemma lem4366442 {_104717 _104718 : Type'} : (term506 _104717 _104718) = (term696 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4366441 _104717 _104718 f)). Qed.
Lemma lem4366443 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4366444 {_104717 _104718 : Type'} : (term507 _104717 _104718) = (term697 _104717 _104718).
Proof. exact (MK_COMB (@lem4366443 _104717) (@lem4366442 _104717 _104718)). Qed.
Lemma lem4366446 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4366447 {_104717 : Type'} (P : type180 _104717) (Q : type180 _104717) : (term674 _104717 P Q) = (term675 _104717 P Q).
Proof. exact (@lem4366446 (type686 _104717) P Q). Qed.
Lemma lem4366448 {_104717 _104718 : Type'} : (term698 _104717 _104718) = (term699 _104717 _104718).
Proof. exact (@lem4366447 _104717 (term700 _104717 _104718) (term701 _104717 _104718)). Qed.
Lemma lem4366449 {_104717 _104718 : Type'} (f : type686 _104717) : (term702 _104717 _104718 f) = (term689 _104717 _104718 f).
Proof. exact (eq_refl (term702 _104717 _104718 f)). Qed.
Lemma lem4366450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366451 {_104717 _104718 : Type'} (f : type686 _104717) : (term703 _104717 _104718 f) = (term691 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366450) (@lem4366449 _104717 _104718 f)). Qed.
Lemma lem4366452 {_104717 _104718 : Type'} (f : type686 _104717) : (term704 _104717 _104718 f) = (term694 _104717 _104718 f).
Proof. exact (eq_refl (term704 _104717 _104718 f)). Qed.
Lemma lem4366453 {_104717 _104718 : Type'} (f : type686 _104717) : (term705 _104717 _104718 f) = (term695 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4366451 _104717 _104718 f) (@lem4366452 _104717 _104718 f)). Qed.
Lemma lem4366454 {_104717 _104718 : Type'} : (term706 _104717 _104718) = (term696 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4366453 _104717 _104718 f)). Qed.
Lemma lem4366455 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4366456 {_104717 _104718 : Type'} : (term698 _104717 _104718) = (term697 _104717 _104718).
Proof. exact (MK_COMB (@lem4366455 _104717) (@lem4366454 _104717 _104718)). Qed.
Lemma lem4366457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4366458 {_104717 _104718 : Type'} : (term707 _104717 _104718) = (term708 _104717 _104718).
Proof. exact (MK_COMB (@lem4366457) (@lem4366456 _104717 _104718)). Qed.
Lemma lem4366459 {_104717 _104718 : Type'} (f : type686 _104717) : (term702 _104717 _104718 f) = (term689 _104717 _104718 f).
Proof. exact (eq_refl (term702 _104717 _104718 f)). Qed.
Lemma lem4366460 {_104717 _104718 : Type'} : (term709 _104717 _104718) = (term700 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4366459 _104717 _104718 f)). Qed.
Lemma lem4366461 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4366462 {_104717 _104718 : Type'} : (term710 _104717 _104718) = (term711 _104717 _104718).
Proof. exact (MK_COMB (@lem4366461 _104717) (@lem4366460 _104717 _104718)). Qed.
Lemma lem4366463 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366464 {_104717 _104718 : Type'} : (term712 _104717 _104718) = (term713 _104717 _104718).
Proof. exact (MK_COMB (@lem4366463) (@lem4366462 _104717 _104718)). Qed.
Lemma lem4366465 {_104717 _104718 : Type'} (f : type686 _104717) : (term704 _104717 _104718 f) = (term694 _104717 _104718 f).
Proof. exact (eq_refl (term704 _104717 _104718 f)). Qed.
Lemma lem4366466 {_104717 _104718 : Type'} : (term714 _104717 _104718) = (term701 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4366465 _104717 _104718 f)). Qed.
Lemma lem4366467 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4366468 {_104717 _104718 : Type'} : (term715 _104717 _104718) = (term716 _104717 _104718).
Proof. exact (MK_COMB (@lem4366467 _104717) (@lem4366466 _104717 _104718)). Qed.
Lemma lem4366469 {_104717 _104718 : Type'} : (term699 _104717 _104718) = (term717 _104717 _104718).
Proof. exact (MK_COMB (@lem4366464 _104717 _104718) (@lem4366468 _104717 _104718)). Qed.
Lemma lem4366470 {_104717 _104718 : Type'} : ((term698 _104717 _104718) = (term699 _104717 _104718)) = ((term697 _104717 _104718) = (term717 _104717 _104718)).
Proof. exact (MK_COMB (@lem4366458 _104717 _104718) (@lem4366469 _104717 _104718)). Qed.
Lemma lem4366471 {_104717 _104718 : Type'} : (term697 _104717 _104718) = (term717 _104717 _104718).
Proof. exact (EQ_MP (@lem4366470 _104717 _104718) (@lem4366448 _104717 _104718)). Qed.
Lemma lem4366848 {_104717 _104718 : Type'} : (term507 _104717 _104718) = (term717 _104717 _104718).
Proof. exact (TRANS (@lem4366444 _104717 _104718) (@lem4366471 _104717 _104718)). Qed.
Lemma lem4366849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366850 {_104717 _104718 : Type'} : (term625 _104717 _104718) = (term718 _104717 _104718).
Proof. exact (MK_COMB (@lem4366849) (@lem4366848 _104717 _104718)). Qed.
Lemma lem4366864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4366865 {_104758 : Type'} (P : _104758 -> Prop) (Q : _104758 -> Prop) : (term628 _104758 P Q) = (term629 _104758 P Q).
Proof. exact (@lem4366864 _104758 P Q). Qed.
Lemma lem4366866 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term719 _104757 _104758 f s p1) = (term720 _104757 _104758 f s p1).
Proof. exact (@lem4366865 _104758 (term721 _104757 _104758 f s p1) (term722 _104757 _104758 f s p1)). Qed.
Lemma lem4366867 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term723 _104757 _104758 f s p1 p2) = (term529 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term723 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366869 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term724 _104757 _104758 f s p1 p2) = (term531 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4366868) (@lem4366867 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366870 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term725 _104757 _104758 f s p1 p2) = (term526 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term725 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366871 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term726 _104757 _104758 f s p1 p2) = (term533 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4366869 _104757 _104758 f s p1 p2) (@lem4366870 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366872 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term727 _104757 _104758 f s p1) = (term540 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4366871 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366873 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4366874 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term719 _104757 _104758 f s p1) = (term541 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366873 _104758) (@lem4366872 _104757 _104758 f s p1)). Qed.
Lemma lem4366875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4366876 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term728 _104757 _104758 f s p1) = (term729 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366875) (@lem4366874 _104757 _104758 f s p1)). Qed.
Lemma lem4366877 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term723 _104757 _104758 f s p1 p2) = (term529 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term723 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366878 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term730 _104757 _104758 f s p1) = (term721 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4366877 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366879 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4366880 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term731 _104757 _104758 f s p1) = (term732 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366879 _104758) (@lem4366878 _104757 _104758 f s p1)). Qed.
Lemma lem4366881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4366882 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term733 _104757 _104758 f s p1) = (term734 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366881) (@lem4366880 _104757 _104758 f s p1)). Qed.
Lemma lem4366883 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term725 _104757 _104758 f s p1 p2) = (term526 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term725 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366884 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term735 _104757 _104758 f s p1) = (term722 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4366883 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4366885 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4366886 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term736 _104757 _104758 f s p1) = (term737 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366885 _104758) (@lem4366884 _104757 _104758 f s p1)). Qed.
Lemma lem4366887 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term720 _104757 _104758 f s p1) = (term738 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4366882 _104757 _104758 f s p1) (@lem4366886 _104757 _104758 f s p1)). Qed.
Lemma lem4366888 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : ((term719 _104757 _104758 f s p1) = (term720 _104757 _104758 f s p1)) = ((term541 _104757 _104758 f s p1) = (term738 _104757 _104758 f s p1)).
Proof. exact (MK_COMB (@lem4366876 _104757 _104758 f s p1) (@lem4366887 _104757 _104758 f s p1)). Qed.
Lemma lem4366889 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term541 _104757 _104758 f s p1) = (term738 _104757 _104758 f s p1).
Proof. exact (EQ_MP (@lem4366888 _104757 _104758 f s p1) (@lem4366866 _104757 _104758 f s p1)). Qed.
Lemma lem4367138 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term547 _104757 _104758 f s) = (term739 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4366889 _104757 _104758 f s p1)). Qed.
Lemma lem4367139 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4367140 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term548 _104757 _104758 f s) = (term740 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367139 _104757) (@lem4367138 _104757 _104758 f s)). Qed.
Lemma lem4367142 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4367143 {_104757 : Type'} (P : _104757 -> Prop) (Q : _104757 -> Prop) : (term628 _104757 P Q) = (term629 _104757 P Q).
Proof. exact (@lem4367142 _104757 P Q). Qed.
Lemma lem4367144 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term741 _104757 _104758 f s) = (term742 _104757 _104758 f s).
Proof. exact (@lem4367143 _104757 (term743 _104757 _104758 f s) (term744 _104757 _104758 f s)). Qed.
Lemma lem4367145 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term745 _104757 _104758 f s p1) = (term732 _104757 _104758 f s p1).
Proof. exact (eq_refl (term745 _104757 _104758 f s p1)). Qed.
Lemma lem4367146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367147 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term746 _104757 _104758 f s p1) = (term734 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4367146) (@lem4367145 _104757 _104758 f s p1)). Qed.
Lemma lem4367148 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term747 _104757 _104758 f s p1) = (term737 _104757 _104758 f s p1).
Proof. exact (eq_refl (term747 _104757 _104758 f s p1)). Qed.
Lemma lem4367149 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term748 _104757 _104758 f s p1) = (term738 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4367147 _104757 _104758 f s p1) (@lem4367148 _104757 _104758 f s p1)). Qed.
Lemma lem4367150 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term749 _104757 _104758 f s) = (term739 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4367149 _104757 _104758 f s p1)). Qed.
Lemma lem4367151 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4367152 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term741 _104757 _104758 f s) = (term740 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367151 _104757) (@lem4367150 _104757 _104758 f s)). Qed.
Lemma lem4367153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4367154 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term750 _104757 _104758 f s) = (term751 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367153) (@lem4367152 _104757 _104758 f s)). Qed.
Lemma lem4367155 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term745 _104757 _104758 f s p1) = (term732 _104757 _104758 f s p1).
Proof. exact (eq_refl (term745 _104757 _104758 f s p1)). Qed.
Lemma lem4367156 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term752 _104757 _104758 f s) = (term743 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4367155 _104757 _104758 f s p1)). Qed.
Lemma lem4367157 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4367158 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term753 _104757 _104758 f s) = (term754 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367157 _104757) (@lem4367156 _104757 _104758 f s)). Qed.
Lemma lem4367159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367160 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term755 _104757 _104758 f s) = (term756 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367159) (@lem4367158 _104757 _104758 f s)). Qed.
Lemma lem4367161 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term747 _104757 _104758 f s p1) = (term737 _104757 _104758 f s p1).
Proof. exact (eq_refl (term747 _104757 _104758 f s p1)). Qed.
Lemma lem4367162 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term757 _104757 _104758 f s) = (term744 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4367161 _104757 _104758 f s p1)). Qed.
Lemma lem4367163 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4367164 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term758 _104757 _104758 f s) = (term759 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367163 _104757) (@lem4367162 _104757 _104758 f s)). Qed.
Lemma lem4367165 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term742 _104757 _104758 f s) = (term760 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367160 _104757 _104758 f s) (@lem4367164 _104757 _104758 f s)). Qed.
Lemma lem4367166 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term741 _104757 _104758 f s) = (term742 _104757 _104758 f s)) = ((term740 _104757 _104758 f s) = (term760 _104757 _104758 f s)).
Proof. exact (MK_COMB (@lem4367154 _104757 _104758 f s) (@lem4367165 _104757 _104758 f s)). Qed.
Lemma lem4367167 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term740 _104757 _104758 f s) = (term760 _104757 _104758 f s).
Proof. exact (EQ_MP (@lem4367166 _104757 _104758 f s) (@lem4367144 _104757 _104758 f s)). Qed.
Lemma lem4367424 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term548 _104757 _104758 f s) = (term760 _104757 _104758 f s).
Proof. exact (TRANS (@lem4367140 _104757 _104758 f s) (@lem4367167 _104757 _104758 f s)). Qed.
Lemma lem4367425 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term554 _104757 _104758 s) = (term761 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4367424 _104757 _104758 f s)). Qed.
Lemma lem4367426 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4367427 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term555 _104757 _104758 s) = (term762 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367426 _104758) (@lem4367425 _104757 _104758 s)). Qed.
Lemma lem4367429 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4367430 {_104758 : Type'} (P : type180 _104758) (Q : type180 _104758) : (term674 _104758 P Q) = (term675 _104758 P Q).
Proof. exact (@lem4367429 (type686 _104758) P Q). Qed.
Lemma lem4367431 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term763 _104757 _104758 s) = (term764 _104757 _104758 s).
Proof. exact (@lem4367430 _104758 (term765 _104757 _104758 s) (term766 _104757 _104758 s)). Qed.
Lemma lem4367432 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term767 _104757 _104758 s f) = (term754 _104757 _104758 f s).
Proof. exact (eq_refl (term767 _104757 _104758 s f)). Qed.
Lemma lem4367433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367434 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term768 _104757 _104758 s f) = (term756 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367433) (@lem4367432 _104757 _104758 f s)). Qed.
Lemma lem4367435 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term769 _104757 _104758 s f) = (term759 _104757 _104758 f s).
Proof. exact (eq_refl (term769 _104757 _104758 s f)). Qed.
Lemma lem4367436 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term770 _104757 _104758 s f) = (term760 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4367434 _104757 _104758 f s) (@lem4367435 _104757 _104758 f s)). Qed.
Lemma lem4367437 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term771 _104757 _104758 s) = (term761 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4367436 _104757 _104758 f s)). Qed.
Lemma lem4367438 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4367439 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term763 _104757 _104758 s) = (term762 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367438 _104758) (@lem4367437 _104757 _104758 s)). Qed.
Lemma lem4367440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4367441 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term772 _104757 _104758 s) = (term773 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367440) (@lem4367439 _104757 _104758 s)). Qed.
Lemma lem4367442 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term767 _104757 _104758 s f) = (term754 _104757 _104758 f s).
Proof. exact (eq_refl (term767 _104757 _104758 s f)). Qed.
Lemma lem4367443 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term774 _104757 _104758 s) = (term765 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4367442 _104757 _104758 f s)). Qed.
Lemma lem4367444 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4367445 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term775 _104757 _104758 s) = (term776 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367444 _104758) (@lem4367443 _104757 _104758 s)). Qed.
Lemma lem4367446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367447 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term777 _104757 _104758 s) = (term778 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367446) (@lem4367445 _104757 _104758 s)). Qed.
Lemma lem4367448 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term769 _104757 _104758 s f) = (term759 _104757 _104758 f s).
Proof. exact (eq_refl (term769 _104757 _104758 s f)). Qed.
Lemma lem4367449 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term779 _104757 _104758 s) = (term766 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4367448 _104757 _104758 f s)). Qed.
Lemma lem4367450 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4367451 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term780 _104757 _104758 s) = (term781 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367450 _104758) (@lem4367449 _104757 _104758 s)). Qed.
Lemma lem4367452 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term764 _104757 _104758 s) = (term782 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367447 _104757 _104758 s) (@lem4367451 _104757 _104758 s)). Qed.
Lemma lem4367453 {_104757 _104758 : Type'} (s : _104757 -> Prop) : ((term763 _104757 _104758 s) = (term764 _104757 _104758 s)) = ((term762 _104757 _104758 s) = (term782 _104757 _104758 s)).
Proof. exact (MK_COMB (@lem4367441 _104757 _104758 s) (@lem4367452 _104757 _104758 s)). Qed.
Lemma lem4367454 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term762 _104757 _104758 s) = (term782 _104757 _104758 s).
Proof. exact (EQ_MP (@lem4367453 _104757 _104758 s) (@lem4367431 _104757 _104758 s)). Qed.
Lemma lem4367719 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term555 _104757 _104758 s) = (term782 _104757 _104758 s).
Proof. exact (TRANS (@lem4367427 _104757 _104758 s) (@lem4367454 _104757 _104758 s)). Qed.
Lemma lem4367720 {_104757 _104758 : Type'} : (term563 _104757 _104758) = (term783 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4367719 _104757 _104758 s)). Qed.
Lemma lem4367721 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4367722 {_104757 _104758 : Type'} : (term564 _104757 _104758) = (term784 _104757 _104758).
Proof. exact (MK_COMB (@lem4367721 _104757) (@lem4367720 _104757 _104758)). Qed.
Lemma lem4367724 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4367725 {_104757 : Type'} (P : type686 _104757) (Q : type686 _104757) : (term785 _104757 P Q) = (term786 _104757 P Q).
Proof. exact (@lem4367724 (_104757 -> Prop) P Q). Qed.
Lemma lem4367726 {_104757 _104758 : Type'} : (term787 _104757 _104758) = (term788 _104757 _104758).
Proof. exact (@lem4367725 _104757 (term789 _104757 _104758) (term790 _104757 _104758)). Qed.
Lemma lem4367727 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term791 _104757 _104758 s) = (term776 _104757 _104758 s).
Proof. exact (eq_refl (term791 _104757 _104758 s)). Qed.
Lemma lem4367728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367729 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term792 _104757 _104758 s) = (term778 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367728) (@lem4367727 _104757 _104758 s)). Qed.
Lemma lem4367730 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term793 _104757 _104758 s) = (term781 _104757 _104758 s).
Proof. exact (eq_refl (term793 _104757 _104758 s)). Qed.
Lemma lem4367731 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term794 _104757 _104758 s) = (term782 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4367729 _104757 _104758 s) (@lem4367730 _104757 _104758 s)). Qed.
Lemma lem4367732 {_104757 _104758 : Type'} : (term795 _104757 _104758) = (term783 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4367731 _104757 _104758 s)). Qed.
Lemma lem4367733 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4367734 {_104757 _104758 : Type'} : (term787 _104757 _104758) = (term784 _104757 _104758).
Proof. exact (MK_COMB (@lem4367733 _104757) (@lem4367732 _104757 _104758)). Qed.
Lemma lem4367735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4367736 {_104757 _104758 : Type'} : (term796 _104757 _104758) = (term797 _104757 _104758).
Proof. exact (MK_COMB (@lem4367735) (@lem4367734 _104757 _104758)). Qed.
Lemma lem4367737 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term791 _104757 _104758 s) = (term776 _104757 _104758 s).
Proof. exact (eq_refl (term791 _104757 _104758 s)). Qed.
Lemma lem4367738 {_104757 _104758 : Type'} : (term798 _104757 _104758) = (term789 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4367737 _104757 _104758 s)). Qed.
Lemma lem4367739 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4367740 {_104757 _104758 : Type'} : (term799 _104757 _104758) = (term800 _104757 _104758).
Proof. exact (MK_COMB (@lem4367739 _104757) (@lem4367738 _104757 _104758)). Qed.
Lemma lem4367741 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4367742 {_104757 _104758 : Type'} : (term801 _104757 _104758) = (term802 _104757 _104758).
Proof. exact (MK_COMB (@lem4367741) (@lem4367740 _104757 _104758)). Qed.
Lemma lem4367743 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term793 _104757 _104758 s) = (term781 _104757 _104758 s).
Proof. exact (eq_refl (term793 _104757 _104758 s)). Qed.
Lemma lem4367744 {_104757 _104758 : Type'} : (term803 _104757 _104758) = (term790 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4367743 _104757 _104758 s)). Qed.
Lemma lem4367745 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4367746 {_104757 _104758 : Type'} : (term804 _104757 _104758) = (term805 _104757 _104758).
Proof. exact (MK_COMB (@lem4367745 _104757) (@lem4367744 _104757 _104758)). Qed.
Lemma lem4367747 {_104757 _104758 : Type'} : (term788 _104757 _104758) = (term806 _104757 _104758).
Proof. exact (MK_COMB (@lem4367742 _104757 _104758) (@lem4367746 _104757 _104758)). Qed.
Lemma lem4367748 {_104757 _104758 : Type'} : ((term787 _104757 _104758) = (term788 _104757 _104758)) = ((term784 _104757 _104758) = (term806 _104757 _104758)).
Proof. exact (MK_COMB (@lem4367736 _104757 _104758) (@lem4367747 _104757 _104758)). Qed.
Lemma lem4367749 {_104757 _104758 : Type'} : (term784 _104757 _104758) = (term806 _104757 _104758).
Proof. exact (EQ_MP (@lem4367748 _104757 _104758) (@lem4367726 _104757 _104758)). Qed.
Lemma lem4368022 {_104757 _104758 : Type'} : (term564 _104757 _104758) = (term806 _104757 _104758).
Proof. exact (TRANS (@lem4367722 _104757 _104758) (@lem4367749 _104757 _104758)). Qed.
Lemma lem4368023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368024 {_104757 _104758 : Type'} : (term620 _104757 _104758) = (term807 _104757 _104758).
Proof. exact (MK_COMB (@lem4368023) (@lem4368022 _104757 _104758)). Qed.
Lemma lem4368038 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4368039 {_104796 : Type'} (P : _104796 -> Prop) (Q : _104796 -> Prop) : (term628 _104796 P Q) = (term629 _104796 P Q).
Proof. exact (@lem4368038 _104796 P Q). Qed.
Lemma lem4368040 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term808 _104795 _104796 f p1 t) = (term809 _104795 _104796 f p1 t).
Proof. exact (@lem4368039 _104796 (term810 _104795 _104796 f p1 t) (term811 _104795 _104796 f p1 t)). Qed.
Lemma lem4368041 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term812 _104795 _104796 f p1 t p2) = (term585 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term812 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368042 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368043 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term813 _104795 _104796 f p1 t p2) = (term587 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4368042) (@lem4368041 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368044 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term814 _104795 _104796 f p1 t p2) = (term582 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term814 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368045 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term815 _104795 _104796 f p1 t p2) = (term589 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4368043 _104795 _104796 f p1 t p2) (@lem4368044 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368046 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term816 _104795 _104796 f p1 t) = (term596 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4368045 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368047 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4368048 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term808 _104795 _104796 f p1 t) = (term597 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368047 _104796) (@lem4368046 _104795 _104796 f p1 t)). Qed.
Lemma lem4368049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4368050 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term817 _104795 _104796 f p1 t) = (term818 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368049) (@lem4368048 _104795 _104796 f p1 t)). Qed.
Lemma lem4368051 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term812 _104795 _104796 f p1 t p2) = (term585 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term812 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368052 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term819 _104795 _104796 f p1 t) = (term810 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4368051 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368053 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4368054 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term820 _104795 _104796 f p1 t) = (term821 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368053 _104796) (@lem4368052 _104795 _104796 f p1 t)). Qed.
Lemma lem4368055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368056 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term822 _104795 _104796 f p1 t) = (term823 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368055) (@lem4368054 _104795 _104796 f p1 t)). Qed.
Lemma lem4368057 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term814 _104795 _104796 f p1 t p2) = (term582 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term814 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368058 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term824 _104795 _104796 f p1 t) = (term811 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4368057 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4368059 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4368060 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term825 _104795 _104796 f p1 t) = (term826 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368059 _104796) (@lem4368058 _104795 _104796 f p1 t)). Qed.
Lemma lem4368061 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term809 _104795 _104796 f p1 t) = (term827 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368056 _104795 _104796 f p1 t) (@lem4368060 _104795 _104796 f p1 t)). Qed.
Lemma lem4368062 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : ((term808 _104795 _104796 f p1 t) = (term809 _104795 _104796 f p1 t)) = ((term597 _104795 _104796 f p1 t) = (term827 _104795 _104796 f p1 t)).
Proof. exact (MK_COMB (@lem4368050 _104795 _104796 f p1 t) (@lem4368061 _104795 _104796 f p1 t)). Qed.
Lemma lem4368063 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term597 _104795 _104796 f p1 t) = (term827 _104795 _104796 f p1 t).
Proof. exact (EQ_MP (@lem4368062 _104795 _104796 f p1 t) (@lem4368040 _104795 _104796 f p1 t)). Qed.
Lemma lem4368312 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term603 _104795 _104796 f t) = (term828 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4368063 _104795 _104796 f p1 t)). Qed.
Lemma lem4368313 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4368314 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term604 _104795 _104796 f t) = (term829 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368313 _104795) (@lem4368312 _104795 _104796 f t)). Qed.
Lemma lem4368316 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4368317 {_104795 : Type'} (P : _104795 -> Prop) (Q : _104795 -> Prop) : (term628 _104795 P Q) = (term629 _104795 P Q).
Proof. exact (@lem4368316 _104795 P Q). Qed.
Lemma lem4368318 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term830 _104795 _104796 f t) = (term831 _104795 _104796 f t).
Proof. exact (@lem4368317 _104795 (term832 _104795 _104796 f t) (term833 _104795 _104796 f t)). Qed.
Lemma lem4368319 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term834 _104795 _104796 f t p1) = (term821 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term834 _104795 _104796 f t p1)). Qed.
Lemma lem4368320 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368321 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term835 _104795 _104796 f t p1) = (term823 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368320) (@lem4368319 _104795 _104796 f p1 t)). Qed.
Lemma lem4368322 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term836 _104795 _104796 f t p1) = (term826 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term836 _104795 _104796 f t p1)). Qed.
Lemma lem4368323 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term837 _104795 _104796 f t p1) = (term827 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4368321 _104795 _104796 f p1 t) (@lem4368322 _104795 _104796 f p1 t)). Qed.
Lemma lem4368324 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term838 _104795 _104796 f t) = (term828 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4368323 _104795 _104796 f p1 t)). Qed.
Lemma lem4368325 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4368326 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term830 _104795 _104796 f t) = (term829 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368325 _104795) (@lem4368324 _104795 _104796 f t)). Qed.
Lemma lem4368327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4368328 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term839 _104795 _104796 f t) = (term840 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368327) (@lem4368326 _104795 _104796 f t)). Qed.
Lemma lem4368329 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term834 _104795 _104796 f t p1) = (term821 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term834 _104795 _104796 f t p1)). Qed.
Lemma lem4368330 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term841 _104795 _104796 f t) = (term832 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4368329 _104795 _104796 f p1 t)). Qed.
Lemma lem4368331 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4368332 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term842 _104795 _104796 f t) = (term843 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368331 _104795) (@lem4368330 _104795 _104796 f t)). Qed.
Lemma lem4368333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368334 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term844 _104795 _104796 f t) = (term845 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368333) (@lem4368332 _104795 _104796 f t)). Qed.
Lemma lem4368335 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term836 _104795 _104796 f t p1) = (term826 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term836 _104795 _104796 f t p1)). Qed.
Lemma lem4368336 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term846 _104795 _104796 f t) = (term833 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4368335 _104795 _104796 f p1 t)). Qed.
Lemma lem4368337 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4368338 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term847 _104795 _104796 f t) = (term848 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368337 _104795) (@lem4368336 _104795 _104796 f t)). Qed.
Lemma lem4368339 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term831 _104795 _104796 f t) = (term849 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368334 _104795 _104796 f t) (@lem4368338 _104795 _104796 f t)). Qed.
Lemma lem4368340 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term830 _104795 _104796 f t) = (term831 _104795 _104796 f t)) = ((term829 _104795 _104796 f t) = (term849 _104795 _104796 f t)).
Proof. exact (MK_COMB (@lem4368328 _104795 _104796 f t) (@lem4368339 _104795 _104796 f t)). Qed.
Lemma lem4368341 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term829 _104795 _104796 f t) = (term849 _104795 _104796 f t).
Proof. exact (EQ_MP (@lem4368340 _104795 _104796 f t) (@lem4368318 _104795 _104796 f t)). Qed.
Lemma lem4368598 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term604 _104795 _104796 f t) = (term849 _104795 _104796 f t).
Proof. exact (TRANS (@lem4368314 _104795 _104796 f t) (@lem4368341 _104795 _104796 f t)). Qed.
Lemma lem4368599 {_104795 _104796 : Type'} (f : type686 _104795) : (term610 _104795 _104796 f) = (term850 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4368598 _104795 _104796 f t)). Qed.
Lemma lem4368600 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4368601 {_104795 _104796 : Type'} (f : type686 _104795) : (term611 _104795 _104796 f) = (term851 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368600 _104796) (@lem4368599 _104795 _104796 f)). Qed.
Lemma lem4368603 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4368604 {_104796 : Type'} (P : type686 _104796) (Q : type686 _104796) : (term785 _104796 P Q) = (term786 _104796 P Q).
Proof. exact (@lem4368603 (_104796 -> Prop) P Q). Qed.
Lemma lem4368605 {_104795 _104796 : Type'} (f : type686 _104795) : (term852 _104795 _104796 f) = (term853 _104795 _104796 f).
Proof. exact (@lem4368604 _104796 (term854 _104795 _104796 f) (term855 _104795 _104796 f)). Qed.
Lemma lem4368606 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term856 _104795 _104796 f t) = (term843 _104795 _104796 f t).
Proof. exact (eq_refl (term856 _104795 _104796 f t)). Qed.
Lemma lem4368607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368608 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term857 _104795 _104796 f t) = (term845 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368607) (@lem4368606 _104795 _104796 f t)). Qed.
Lemma lem4368609 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term858 _104795 _104796 f t) = (term848 _104795 _104796 f t).
Proof. exact (eq_refl (term858 _104795 _104796 f t)). Qed.
Lemma lem4368610 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term859 _104795 _104796 f t) = (term849 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4368608 _104795 _104796 f t) (@lem4368609 _104795 _104796 f t)). Qed.
Lemma lem4368611 {_104795 _104796 : Type'} (f : type686 _104795) : (term860 _104795 _104796 f) = (term850 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4368610 _104795 _104796 f t)). Qed.
Lemma lem4368612 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4368613 {_104795 _104796 : Type'} (f : type686 _104795) : (term852 _104795 _104796 f) = (term851 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368612 _104796) (@lem4368611 _104795 _104796 f)). Qed.
Lemma lem4368614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4368615 {_104795 _104796 : Type'} (f : type686 _104795) : (term861 _104795 _104796 f) = (term862 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368614) (@lem4368613 _104795 _104796 f)). Qed.
Lemma lem4368616 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term856 _104795 _104796 f t) = (term843 _104795 _104796 f t).
Proof. exact (eq_refl (term856 _104795 _104796 f t)). Qed.
Lemma lem4368617 {_104795 _104796 : Type'} (f : type686 _104795) : (term863 _104795 _104796 f) = (term854 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4368616 _104795 _104796 f t)). Qed.
Lemma lem4368618 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4368619 {_104795 _104796 : Type'} (f : type686 _104795) : (term864 _104795 _104796 f) = (term865 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368618 _104796) (@lem4368617 _104795 _104796 f)). Qed.
Lemma lem4368620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368621 {_104795 _104796 : Type'} (f : type686 _104795) : (term866 _104795 _104796 f) = (term867 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368620) (@lem4368619 _104795 _104796 f)). Qed.
Lemma lem4368622 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term858 _104795 _104796 f t) = (term848 _104795 _104796 f t).
Proof. exact (eq_refl (term858 _104795 _104796 f t)). Qed.
Lemma lem4368623 {_104795 _104796 : Type'} (f : type686 _104795) : (term868 _104795 _104796 f) = (term855 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4368622 _104795 _104796 f t)). Qed.
Lemma lem4368624 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4368625 {_104795 _104796 : Type'} (f : type686 _104795) : (term869 _104795 _104796 f) = (term870 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368624 _104796) (@lem4368623 _104795 _104796 f)). Qed.
Lemma lem4368626 {_104795 _104796 : Type'} (f : type686 _104795) : (term853 _104795 _104796 f) = (term871 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368621 _104795 _104796 f) (@lem4368625 _104795 _104796 f)). Qed.
Lemma lem4368627 {_104795 _104796 : Type'} (f : type686 _104795) : ((term852 _104795 _104796 f) = (term853 _104795 _104796 f)) = ((term851 _104795 _104796 f) = (term871 _104795 _104796 f)).
Proof. exact (MK_COMB (@lem4368615 _104795 _104796 f) (@lem4368626 _104795 _104796 f)). Qed.
Lemma lem4368628 {_104795 _104796 : Type'} (f : type686 _104795) : (term851 _104795 _104796 f) = (term871 _104795 _104796 f).
Proof. exact (EQ_MP (@lem4368627 _104795 _104796 f) (@lem4368605 _104795 _104796 f)). Qed.
Lemma lem4368893 {_104795 _104796 : Type'} (f : type686 _104795) : (term611 _104795 _104796 f) = (term871 _104795 _104796 f).
Proof. exact (TRANS (@lem4368601 _104795 _104796 f) (@lem4368628 _104795 _104796 f)). Qed.
Lemma lem4368894 {_104795 _104796 : Type'} : (term617 _104795 _104796) = (term872 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4368893 _104795 _104796 f)). Qed.
Lemma lem4368895 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4368896 {_104795 _104796 : Type'} : (term618 _104795 _104796) = (term873 _104795 _104796).
Proof. exact (MK_COMB (@lem4368895 _104795) (@lem4368894 _104795 _104796)). Qed.
Lemma lem4368898 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term628 A P Q) = (term629 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4368899 {_104795 : Type'} (P : type180 _104795) (Q : type180 _104795) : (term674 _104795 P Q) = (term675 _104795 P Q).
Proof. exact (@lem4368898 (type686 _104795) P Q). Qed.
Lemma lem4368900 {_104795 _104796 : Type'} : (term874 _104795 _104796) = (term875 _104795 _104796).
Proof. exact (@lem4368899 _104795 (term876 _104795 _104796) (term877 _104795 _104796)). Qed.
Lemma lem4368901 {_104795 _104796 : Type'} (f : type686 _104795) : (term878 _104795 _104796 f) = (term865 _104795 _104796 f).
Proof. exact (eq_refl (term878 _104795 _104796 f)). Qed.
Lemma lem4368902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368903 {_104795 _104796 : Type'} (f : type686 _104795) : (term879 _104795 _104796 f) = (term867 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368902) (@lem4368901 _104795 _104796 f)). Qed.
Lemma lem4368904 {_104795 _104796 : Type'} (f : type686 _104795) : (term880 _104795 _104796 f) = (term870 _104795 _104796 f).
Proof. exact (eq_refl (term880 _104795 _104796 f)). Qed.
Lemma lem4368905 {_104795 _104796 : Type'} (f : type686 _104795) : (term881 _104795 _104796 f) = (term871 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4368903 _104795 _104796 f) (@lem4368904 _104795 _104796 f)). Qed.
Lemma lem4368906 {_104795 _104796 : Type'} : (term882 _104795 _104796) = (term872 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4368905 _104795 _104796 f)). Qed.
Lemma lem4368907 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4368908 {_104795 _104796 : Type'} : (term874 _104795 _104796) = (term873 _104795 _104796).
Proof. exact (MK_COMB (@lem4368907 _104795) (@lem4368906 _104795 _104796)). Qed.
Lemma lem4368909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4368910 {_104795 _104796 : Type'} : (term883 _104795 _104796) = (term884 _104795 _104796).
Proof. exact (MK_COMB (@lem4368909) (@lem4368908 _104795 _104796)). Qed.
Lemma lem4368911 {_104795 _104796 : Type'} (f : type686 _104795) : (term878 _104795 _104796 f) = (term865 _104795 _104796 f).
Proof. exact (eq_refl (term878 _104795 _104796 f)). Qed.
Lemma lem4368912 {_104795 _104796 : Type'} : (term885 _104795 _104796) = (term876 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4368911 _104795 _104796 f)). Qed.
Lemma lem4368913 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4368914 {_104795 _104796 : Type'} : (term886 _104795 _104796) = (term887 _104795 _104796).
Proof. exact (MK_COMB (@lem4368913 _104795) (@lem4368912 _104795 _104796)). Qed.
Lemma lem4368915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4368916 {_104795 _104796 : Type'} : (term888 _104795 _104796) = (term889 _104795 _104796).
Proof. exact (MK_COMB (@lem4368915) (@lem4368914 _104795 _104796)). Qed.
Lemma lem4368917 {_104795 _104796 : Type'} (f : type686 _104795) : (term880 _104795 _104796 f) = (term870 _104795 _104796 f).
Proof. exact (eq_refl (term880 _104795 _104796 f)). Qed.
Lemma lem4368918 {_104795 _104796 : Type'} : (term890 _104795 _104796) = (term877 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4368917 _104795 _104796 f)). Qed.
Lemma lem4368919 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4368920 {_104795 _104796 : Type'} : (term891 _104795 _104796) = (term892 _104795 _104796).
Proof. exact (MK_COMB (@lem4368919 _104795) (@lem4368918 _104795 _104796)). Qed.
Lemma lem4368921 {_104795 _104796 : Type'} : (term875 _104795 _104796) = (term893 _104795 _104796).
Proof. exact (MK_COMB (@lem4368916 _104795 _104796) (@lem4368920 _104795 _104796)). Qed.
Lemma lem4368922 {_104795 _104796 : Type'} : ((term874 _104795 _104796) = (term875 _104795 _104796)) = ((term873 _104795 _104796) = (term893 _104795 _104796)).
Proof. exact (MK_COMB (@lem4368910 _104795 _104796) (@lem4368921 _104795 _104796)). Qed.
Lemma lem4368923 {_104795 _104796 : Type'} : (term873 _104795 _104796) = (term893 _104795 _104796).
Proof. exact (EQ_MP (@lem4368922 _104795 _104796) (@lem4368900 _104795 _104796)). Qed.
Lemma lem4369196 {_104795 _104796 : Type'} : (term618 _104795 _104796) = (term893 _104795 _104796).
Proof. exact (TRANS (@lem4368896 _104795 _104796) (@lem4368923 _104795 _104796)). Qed.
Lemma lem4369197 {_104757 _104758 _104795 _104796 : Type'} : (term622 _104757 _104758 _104795 _104796) = (term894 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4368024 _104757 _104758) (@lem4369196 _104795 _104796)). Qed.
Lemma lem4369198 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term627 _104717 _104718 _104757 _104758 _104795 _104796) = (term895 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4366850 _104717 _104718) (@lem4369197 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4369200 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369201 {_104717 : Type'} (P : type686 _104717) (Q : Prop) : (term898 _104717 P Q) = (term899 _104717 P Q).
Proof. exact (@lem4369200 (_104717 -> Prop) P Q). Qed.
Lemma lem4369202 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term900 _104717 _104718 f p1 g p2) = (term901 _104717 _104718 f p1 g p2).
Proof. exact (@lem4369201 _104717 (term363 _104717 f p1) (term364 _104718 g p2)). Qed.
Lemma lem4369203 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term431 _104717 f p1 t) = (term361 _104717 f t p1).
Proof. exact (eq_refl (term431 _104717 f p1 t)). Qed.
Lemma lem4369204 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term902 _104717 f p1) = (term363 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369203 _104717 f t p1)). Qed.
Lemma lem4369205 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369206 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term903 _104717 f p1) = (term364 _104717 f p1).
Proof. exact (MK_COMB (@lem4369205 _104717) (@lem4369204 _104717 f p1)). Qed.
Lemma lem4369207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369208 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term904 _104717 f p1) = (term366 _104717 f p1).
Proof. exact (MK_COMB (@lem4369207) (@lem4369206 _104717 f p1)). Qed.
Lemma lem4369209 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term364 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (eq_refl (term364 _104718 g p2)). Qed.
Lemma lem4369210 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term900 _104717 _104718 f p1 g p2) = (term367 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369208 _104717 f p1) (@lem4369209 _104718 g p2)). Qed.
Lemma lem4369211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369212 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term905 _104717 _104718 f p1 g p2) = (term368 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369211) (@lem4369210 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369213 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term431 _104717 f p1 t) = (term361 _104717 f t p1).
Proof. exact (eq_refl (term431 _104717 f p1 t)). Qed.
Lemma lem4369214 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369215 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term906 _104717 f p1 t) = (term907 _104717 f t p1).
Proof. exact (MK_COMB (@lem4369214) (@lem4369213 _104717 f t p1)). Qed.
Lemma lem4369216 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term364 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (eq_refl (term364 _104718 g p2)). Qed.
Lemma lem4369217 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term908 _104717 _104718 f p1 t g p2) = (term909 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369215 _104717 f t p1) (@lem4369216 _104718 g p2)). Qed.
Lemma lem4369218 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term910 _104717 _104718 f p1 g p2) = (term911 _104717 _104718 f p1 g p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369217 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369219 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369220 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term901 _104717 _104718 f p1 g p2) = (term912 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369219 _104717) (@lem4369218 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369221 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : ((term900 _104717 _104718 f p1 g p2) = (term901 _104717 _104718 f p1 g p2)) = ((term367 _104717 _104718 f p1 g p2) = (term912 _104717 _104718 f p1 g p2)).
Proof. exact (MK_COMB (@lem4369212 _104717 _104718 f p1 g p2) (@lem4369220 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369222 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term367 _104717 _104718 f p1 g p2) = (term912 _104717 _104718 f p1 g p2).
Proof. exact (EQ_MP (@lem4369221 _104717 _104718 f p1 g p2) (@lem4369202 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369224 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369225 {_104718 : Type'} (P : Prop) (Q : type686 _104718) : (term915 _104718 P Q) = (term916 _104718 P Q).
Proof. exact (@lem4369224 (_104718 -> Prop) P Q). Qed.
Lemma lem4369226 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term917 _104717 _104718 f t p1 g p2) = (term918 _104717 _104718 f t p1 g p2).
Proof. exact (@lem4369225 _104718 (term361 _104717 f t p1) (term363 _104718 g p2)). Qed.
Lemma lem4369227 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term431 _104718 g p2 t) = (term361 _104718 g t p2).
Proof. exact (eq_refl (term431 _104718 g p2 t)). Qed.
Lemma lem4369228 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term902 _104718 g p2) = (term363 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4369227 _104718 g t p2)). Qed.
Lemma lem4369229 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369230 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term903 _104718 g p2) = (term364 _104718 g p2).
Proof. exact (MK_COMB (@lem4369229 _104718) (@lem4369228 _104718 g p2)). Qed.
Lemma lem4369231 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term907 _104717 f t p1) = (term907 _104717 f t p1).
Proof. exact (eq_refl (term907 _104717 f t p1)). Qed.
Lemma lem4369232 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term917 _104717 _104718 f t p1 g p2) = (term909 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369231 _104717 f t p1) (@lem4369230 _104718 g p2)). Qed.
Lemma lem4369233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369234 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term919 _104717 _104718 f t p1 g p2) = (term920 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369233) (@lem4369232 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369235 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term431 _104718 g p2 t) = (term361 _104718 g t p2).
Proof. exact (eq_refl (term431 _104718 g p2 t)). Qed.
Lemma lem4369236 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term907 _104717 f t p1) = (term907 _104717 f t p1).
Proof. exact (eq_refl (term907 _104717 f t p1)). Qed.
Lemma lem4369237 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term921 _104717 _104718 f t p1 g p2 t') = (term922 _104717 _104718 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4369236 _104717 f t p1) (@lem4369235 _104718 g t' p2)). Qed.
Lemma lem4369238 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term923 _104717 _104718 f t p1 g p2) = (term924 _104717 _104718 f t p1 g p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369237 _104717 _104718 f t p1 g t' p2)). Qed.
Lemma lem4369239 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369240 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term918 _104717 _104718 f t p1 g p2) = (term925 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369239 _104718) (@lem4369238 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369241 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : ((term917 _104717 _104718 f t p1 g p2) = (term918 _104717 _104718 f t p1 g p2)) = ((term909 _104717 _104718 f t p1 g p2) = (term925 _104717 _104718 f t p1 g p2)).
Proof. exact (MK_COMB (@lem4369234 _104717 _104718 f t p1 g p2) (@lem4369240 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369242 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term909 _104717 _104718 f t p1 g p2) = (term925 _104717 _104718 f t p1 g p2).
Proof. exact (EQ_MP (@lem4369241 _104717 _104718 f t p1 g p2) (@lem4369226 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369243 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term911 _104717 _104718 f p1 g p2) = (term926 _104717 _104718 f p1 g p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369242 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369244 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369245 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term912 _104717 _104718 f p1 g p2) = (term927 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369244 _104717) (@lem4369243 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369246 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term367 _104717 _104718 f p1 g p2) = (term927 _104717 _104718 f p1 g p2).
Proof. exact (TRANS (@lem4369222 _104717 _104718 f p1 g p2) (@lem4369245 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369248 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term468 _104717 _104718 f p1 g p2) = (term928 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369247) (@lem4369246 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369249 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369250 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term470 _104717 _104718 f g p1 p2) = (term929 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369248 _104717 _104718 f p1 g p2) (@lem4369249 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369252 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369253 {_104717 : Type'} (P : type686 _104717) (Q : Prop) : (term898 _104717 P Q) = (term899 _104717 P Q).
Proof. exact (@lem4369252 (_104717 -> Prop) P Q). Qed.
Lemma lem4369254 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term930 _104717 _104718 f g p1 p2) = (term931 _104717 _104718 f g p1 p2).
Proof. exact (@lem4369253 _104717 (term926 _104717 _104718 f p1 g p2) (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369255 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term932 _104717 _104718 f p1 g p2 t) = (term925 _104717 _104718 f t p1 g p2).
Proof. exact (eq_refl (term932 _104717 _104718 f p1 g p2 t)). Qed.
Lemma lem4369256 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term933 _104717 _104718 f p1 g p2) = (term926 _104717 _104718 f p1 g p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369255 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369257 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369258 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term934 _104717 _104718 f p1 g p2) = (term927 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369257 _104717) (@lem4369256 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369260 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term935 _104717 _104718 f p1 g p2) = (term928 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4369259) (@lem4369258 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369261 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369262 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term930 _104717 _104718 f g p1 p2) = (term929 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369260 _104717 _104718 f p1 g p2) (@lem4369261 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369264 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term936 _104717 _104718 f g p1 p2) = (term937 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369263) (@lem4369262 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369265 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term932 _104717 _104718 f p1 g p2 t) = (term925 _104717 _104718 f t p1 g p2).
Proof. exact (eq_refl (term932 _104717 _104718 f p1 g p2 t)). Qed.
Lemma lem4369266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369267 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term938 _104717 _104718 f p1 g p2 t) = (term939 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369266) (@lem4369265 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369268 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369269 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term940 _104717 _104718 t f g p1 p2) = (term941 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369267 _104717 _104718 f t p1 g p2) (@lem4369268 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369270 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term942 _104717 _104718 f g p1 p2) = (term943 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369269 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369271 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369272 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term931 _104717 _104718 f g p1 p2) = (term944 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369271 _104717) (@lem4369270 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369273 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term930 _104717 _104718 f g p1 p2) = (term931 _104717 _104718 f g p1 p2)) = ((term929 _104717 _104718 f g p1 p2) = (term944 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4369264 _104717 _104718 f g p1 p2) (@lem4369272 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369274 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term929 _104717 _104718 f g p1 p2) = (term944 _104717 _104718 f g p1 p2).
Proof. exact (EQ_MP (@lem4369273 _104717 _104718 f g p1 p2) (@lem4369254 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369276 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369277 {_104718 : Type'} (P : type686 _104718) (Q : Prop) : (term898 _104718 P Q) = (term899 _104718 P Q).
Proof. exact (@lem4369276 (_104718 -> Prop) P Q). Qed.
Lemma lem4369278 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term945 _104717 _104718 t f g p1 p2) = (term946 _104717 _104718 t f g p1 p2).
Proof. exact (@lem4369277 _104718 (term924 _104717 _104718 f t p1 g p2) (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369279 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term947 _104717 _104718 f t p1 g p2 t') = (term922 _104717 _104718 f t p1 g t' p2).
Proof. exact (eq_refl (term947 _104717 _104718 f t p1 g p2 t')). Qed.
Lemma lem4369280 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term948 _104717 _104718 f t p1 g p2) = (term924 _104717 _104718 f t p1 g p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369279 _104717 _104718 f t p1 g t' p2)). Qed.
Lemma lem4369281 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369282 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term949 _104717 _104718 f t p1 g p2) = (term925 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369281 _104718) (@lem4369280 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369284 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term950 _104717 _104718 f t p1 g p2) = (term939 _104717 _104718 f t p1 g p2).
Proof. exact (MK_COMB (@lem4369283) (@lem4369282 _104717 _104718 f t p1 g p2)). Qed.
Lemma lem4369285 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369286 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term945 _104717 _104718 t f g p1 p2) = (term941 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369284 _104717 _104718 f t p1 g p2) (@lem4369285 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369288 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term951 _104717 _104718 t f g p1 p2) = (term952 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369287) (@lem4369286 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369289 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term947 _104717 _104718 f t p1 g p2 t') = (term922 _104717 _104718 f t p1 g t' p2).
Proof. exact (eq_refl (term947 _104717 _104718 f t p1 g p2 t')). Qed.
Lemma lem4369290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369291 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term953 _104717 _104718 f t p1 g p2 t') = (term954 _104717 _104718 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4369290) (@lem4369289 _104717 _104718 f t p1 g t' p2)). Qed.
Lemma lem4369292 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term463 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term463 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369293 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term955 _104717 _104718 t t' f g p1 p2) = (term956 _104717 _104718 t t' f g p1 p2).
Proof. exact (MK_COMB (@lem4369291 _104717 _104718 f t p1 g t' p2) (@lem4369292 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369294 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term957 _104717 _104718 t f g p1 p2) = (term958 _104717 _104718 t f g p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369293 _104717 _104718 t t' f g p1 p2)). Qed.
Lemma lem4369295 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369296 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term946 _104717 _104718 t f g p1 p2) = (term959 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369295 _104718) (@lem4369294 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369297 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term945 _104717 _104718 t f g p1 p2) = (term946 _104717 _104718 t f g p1 p2)) = ((term941 _104717 _104718 t f g p1 p2) = (term959 _104717 _104718 t f g p1 p2)).
Proof. exact (MK_COMB (@lem4369288 _104717 _104718 t f g p1 p2) (@lem4369296 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369298 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term941 _104717 _104718 t f g p1 p2) = (term959 _104717 _104718 t f g p1 p2).
Proof. exact (EQ_MP (@lem4369297 _104717 _104718 t f g p1 p2) (@lem4369278 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369299 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term943 _104717 _104718 f g p1 p2) = (term960 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369298 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369300 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369301 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term944 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369300 _104717) (@lem4369299 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369302 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term929 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4369274 _104717 _104718 f g p1 p2) (@lem4369301 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369303 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term470 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4369250 _104717 _104718 f g p1 p2) (@lem4369302 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369304 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term632 _104717 _104718 f g p1) = (term962 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369303 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369305 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369306 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term643 _104717 _104718 f g p1) = (term963 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369305 _104718) (@lem4369304 _104717 _104718 f g p1)). Qed.
Lemma lem4369307 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term654 _104717 _104718 f g) = (term964 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369306 _104717 _104718 f g p1)). Qed.
Lemma lem4369308 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369309 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term665 _104717 _104718 f g) = (term965 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369308 _104717) (@lem4369307 _104717 _104718 f g)). Qed.
Lemma lem4369310 {_104717 _104718 : Type'} (f : type686 _104717) : (term678 _104717 _104718 f) = (term966 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369309 _104717 _104718 f g)). Qed.
Lemma lem4369311 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369312 {_104717 _104718 : Type'} (f : type686 _104717) : (term689 _104717 _104718 f) = (term967 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369311 _104718) (@lem4369310 _104717 _104718 f)). Qed.
Lemma lem4369313 {_104717 _104718 : Type'} : (term700 _104717 _104718) = (term968 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369312 _104717 _104718 f)). Qed.
Lemma lem4369314 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369315 {_104717 _104718 : Type'} : (term711 _104717 _104718) = (term969 _104717 _104718).
Proof. exact (MK_COMB (@lem4369314 _104717) (@lem4369313 _104717 _104718)). Qed.
Lemma lem4369316 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369317 {_104717 _104718 : Type'} : (term713 _104717 _104718) = (term970 _104717 _104718).
Proof. exact (MK_COMB (@lem4369316) (@lem4369315 _104717 _104718)). Qed.
Lemma lem4369319 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369320 {_104717 : Type'} (P : Prop) (Q : type686 _104717) : (term915 _104717 P Q) = (term916 _104717 P Q).
Proof. exact (@lem4369319 (_104717 -> Prop) P Q). Qed.
Lemma lem4369321 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term971 _104717 _104718 f g p1 p2) = (term972 _104717 _104718 f g p1 p2).
Proof. exact (@lem4369320 _104717 (term439 _104717 _104718 f p1 g p2) (term377 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369322 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term459 _104717 _104718 f g p1 p2 s) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (eq_refl (term459 _104717 _104718 f g p1 p2 s)). Qed.
Lemma lem4369323 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term973 _104717 _104718 f g p1 p2) = (term377 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4369322 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369324 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369325 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term974 _104717 _104718 f g p1 p2) = (term378 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369324 _104717) (@lem4369323 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369326 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term465 _104717 _104718 f p1 g p2) = (term465 _104717 _104718 f p1 g p2).
Proof. exact (eq_refl (term465 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369327 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term971 _104717 _104718 f g p1 p2) = (term467 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369326 _104717 _104718 f p1 g p2) (@lem4369325 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369329 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term975 _104717 _104718 f g p1 p2) = (term976 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369328) (@lem4369327 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369330 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term459 _104717 _104718 f g p1 p2 s) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (eq_refl (term459 _104717 _104718 f g p1 p2 s)). Qed.
Lemma lem4369331 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term465 _104717 _104718 f p1 g p2) = (term465 _104717 _104718 f p1 g p2).
Proof. exact (eq_refl (term465 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369332 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term977 _104717 _104718 f g p1 p2 s) = (term978 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4369331 _104717 _104718 f p1 g p2) (@lem4369330 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369333 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term979 _104717 _104718 f g p1 p2) = (term980 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4369332 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369334 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369335 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term972 _104717 _104718 f g p1 p2) = (term981 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369334 _104717) (@lem4369333 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369336 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term971 _104717 _104718 f g p1 p2) = (term972 _104717 _104718 f g p1 p2)) = ((term467 _104717 _104718 f g p1 p2) = (term981 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4369329 _104717 _104718 f g p1 p2) (@lem4369335 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369337 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term467 _104717 _104718 f g p1 p2) = (term981 _104717 _104718 f g p1 p2).
Proof. exact (EQ_MP (@lem4369336 _104717 _104718 f g p1 p2) (@lem4369321 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369339 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369340 {_104718 : Type'} (P : Prop) (Q : type686 _104718) : (term915 _104718 P Q) = (term916 _104718 P Q).
Proof. exact (@lem4369339 (_104718 -> Prop) P Q). Qed.
Lemma lem4369341 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term982 _104717 _104718 f g s p1 p2) = (term983 _104717 _104718 f g s p1 p2).
Proof. exact (@lem4369340 _104718 (term439 _104717 _104718 f p1 g p2) (term375 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369342 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term452 _104717 _104718 f g s p1 p2 t) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term452 _104717 _104718 f g s p1 p2 t)). Qed.
Lemma lem4369343 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term984 _104717 _104718 f g s p1 p2) = (term375 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4369342 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4369344 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369345 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term985 _104717 _104718 f g s p1 p2) = (term376 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4369344 _104718) (@lem4369343 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369346 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term465 _104717 _104718 f p1 g p2) = (term465 _104717 _104718 f p1 g p2).
Proof. exact (eq_refl (term465 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369347 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term982 _104717 _104718 f g s p1 p2) = (term978 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4369346 _104717 _104718 f p1 g p2) (@lem4369345 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369349 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term986 _104717 _104718 f g s p1 p2) = (term987 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4369348) (@lem4369347 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369350 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term452 _104717 _104718 f g s p1 p2 t) = (term374 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term452 _104717 _104718 f g s p1 p2 t)). Qed.
Lemma lem4369351 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term465 _104717 _104718 f p1 g p2) = (term465 _104717 _104718 f p1 g p2).
Proof. exact (eq_refl (term465 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4369352 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term988 _104717 _104718 f g s p1 p2 t) = (term989 _104717 _104718 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4369351 _104717 _104718 f p1 g p2) (@lem4369350 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4369353 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term990 _104717 _104718 f g s p1 p2) = (term991 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4369352 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4369354 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369355 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term983 _104717 _104718 f g s p1 p2) = (term992 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4369354 _104718) (@lem4369353 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369356 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : ((term982 _104717 _104718 f g s p1 p2) = (term983 _104717 _104718 f g s p1 p2)) = ((term978 _104717 _104718 f g s p1 p2) = (term992 _104717 _104718 f g s p1 p2)).
Proof. exact (MK_COMB (@lem4369349 _104717 _104718 f g s p1 p2) (@lem4369355 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369357 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term978 _104717 _104718 f g s p1 p2) = (term992 _104717 _104718 f g s p1 p2).
Proof. exact (EQ_MP (@lem4369356 _104717 _104718 f g s p1 p2) (@lem4369341 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369358 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term980 _104717 _104718 f g p1 p2) = (term993 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4369357 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4369359 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369360 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term981 _104717 _104718 f g p1 p2) = (term994 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369359 _104717) (@lem4369358 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369361 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term467 _104717 _104718 f g p1 p2) = (term994 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4369337 _104717 _104718 f g p1 p2) (@lem4369360 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369362 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term633 _104717 _104718 f g p1) = (term995 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369361 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369363 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369364 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term648 _104717 _104718 f g p1) = (term996 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369363 _104718) (@lem4369362 _104717 _104718 f g p1)). Qed.
Lemma lem4369365 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term655 _104717 _104718 f g) = (term997 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369364 _104717 _104718 f g p1)). Qed.
Lemma lem4369366 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369367 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term670 _104717 _104718 f g) = (term998 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369366 _104717) (@lem4369365 _104717 _104718 f g)). Qed.
Lemma lem4369368 {_104717 _104718 : Type'} (f : type686 _104717) : (term679 _104717 _104718 f) = (term999 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369367 _104717 _104718 f g)). Qed.
Lemma lem4369369 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369370 {_104717 _104718 : Type'} (f : type686 _104717) : (term694 _104717 _104718 f) = (term1000 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369369 _104718) (@lem4369368 _104717 _104718 f)). Qed.
Lemma lem4369371 {_104717 _104718 : Type'} : (term701 _104717 _104718) = (term1001 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369370 _104717 _104718 f)). Qed.
Lemma lem4369372 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369373 {_104717 _104718 : Type'} : (term716 _104717 _104718) = (term1002 _104717 _104718).
Proof. exact (MK_COMB (@lem4369372 _104717) (@lem4369371 _104717 _104718)). Qed.
Lemma lem4369374 {_104717 _104718 : Type'} : (term717 _104717 _104718) = (term1003 _104717 _104718).
Proof. exact (MK_COMB (@lem4369317 _104717 _104718) (@lem4369373 _104717 _104718)). Qed.
Lemma lem4369376 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369377 {_104717 : Type'} (P : type180 _104717) (Q : type180 _104717) : (term675 _104717 P Q) = (term674 _104717 P Q).
Proof. exact (@lem4369376 (type686 _104717) P Q). Qed.
Lemma lem4369378 {_104717 _104718 : Type'} : (term1004 _104717 _104718) = (term1005 _104717 _104718).
Proof. exact (@lem4369377 _104717 (term968 _104717 _104718) (term1001 _104717 _104718)). Qed.
Lemma lem4369379 {_104717 _104718 : Type'} (f : type686 _104717) : (term1006 _104717 _104718 f) = (term967 _104717 _104718 f).
Proof. exact (eq_refl (term1006 _104717 _104718 f)). Qed.
Lemma lem4369380 {_104717 _104718 : Type'} : (term1007 _104717 _104718) = (term968 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369379 _104717 _104718 f)). Qed.
Lemma lem4369381 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369382 {_104717 _104718 : Type'} : (term1008 _104717 _104718) = (term969 _104717 _104718).
Proof. exact (MK_COMB (@lem4369381 _104717) (@lem4369380 _104717 _104718)). Qed.
Lemma lem4369383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369384 {_104717 _104718 : Type'} : (term1009 _104717 _104718) = (term970 _104717 _104718).
Proof. exact (MK_COMB (@lem4369383) (@lem4369382 _104717 _104718)). Qed.
Lemma lem4369385 {_104717 _104718 : Type'} (f : type686 _104717) : (term1010 _104717 _104718 f) = (term1000 _104717 _104718 f).
Proof. exact (eq_refl (term1010 _104717 _104718 f)). Qed.
Lemma lem4369386 {_104717 _104718 : Type'} : (term1011 _104717 _104718) = (term1001 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369385 _104717 _104718 f)). Qed.
Lemma lem4369387 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369388 {_104717 _104718 : Type'} : (term1012 _104717 _104718) = (term1002 _104717 _104718).
Proof. exact (MK_COMB (@lem4369387 _104717) (@lem4369386 _104717 _104718)). Qed.
Lemma lem4369389 {_104717 _104718 : Type'} : (term1004 _104717 _104718) = (term1003 _104717 _104718).
Proof. exact (MK_COMB (@lem4369384 _104717 _104718) (@lem4369388 _104717 _104718)). Qed.
Lemma lem4369390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369391 {_104717 _104718 : Type'} : (term1013 _104717 _104718) = (term1014 _104717 _104718).
Proof. exact (MK_COMB (@lem4369390) (@lem4369389 _104717 _104718)). Qed.
Lemma lem4369392 {_104717 _104718 : Type'} (f : type686 _104717) : (term1006 _104717 _104718 f) = (term967 _104717 _104718 f).
Proof. exact (eq_refl (term1006 _104717 _104718 f)). Qed.
Lemma lem4369393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369394 {_104717 _104718 : Type'} (f : type686 _104717) : (term1015 _104717 _104718 f) = (term1016 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369393) (@lem4369392 _104717 _104718 f)). Qed.
Lemma lem4369395 {_104717 _104718 : Type'} (f : type686 _104717) : (term1010 _104717 _104718 f) = (term1000 _104717 _104718 f).
Proof. exact (eq_refl (term1010 _104717 _104718 f)). Qed.
Lemma lem4369396 {_104717 _104718 : Type'} (f : type686 _104717) : (term1017 _104717 _104718 f) = (term1018 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369394 _104717 _104718 f) (@lem4369395 _104717 _104718 f)). Qed.
Lemma lem4369397 {_104717 _104718 : Type'} : (term1019 _104717 _104718) = (term1020 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369396 _104717 _104718 f)). Qed.
Lemma lem4369398 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369399 {_104717 _104718 : Type'} : (term1005 _104717 _104718) = (term1021 _104717 _104718).
Proof. exact (MK_COMB (@lem4369398 _104717) (@lem4369397 _104717 _104718)). Qed.
Lemma lem4369400 {_104717 _104718 : Type'} : ((term1004 _104717 _104718) = (term1005 _104717 _104718)) = ((term1003 _104717 _104718) = (term1021 _104717 _104718)).
Proof. exact (MK_COMB (@lem4369391 _104717 _104718) (@lem4369399 _104717 _104718)). Qed.
Lemma lem4369401 {_104717 _104718 : Type'} : (term1003 _104717 _104718) = (term1021 _104717 _104718).
Proof. exact (EQ_MP (@lem4369400 _104717 _104718) (@lem4369378 _104717 _104718)). Qed.
Lemma lem4369403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369404 {_104718 : Type'} (P : type180 _104718) (Q : type180 _104718) : (term675 _104718 P Q) = (term674 _104718 P Q).
Proof. exact (@lem4369403 (type686 _104718) P Q). Qed.
Lemma lem4369405 {_104717 _104718 : Type'} (f : type686 _104717) : (term1022 _104717 _104718 f) = (term1023 _104717 _104718 f).
Proof. exact (@lem4369404 _104718 (term966 _104717 _104718 f) (term999 _104717 _104718 f)). Qed.
Lemma lem4369406 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1024 _104717 _104718 f g) = (term965 _104717 _104718 f g).
Proof. exact (eq_refl (term1024 _104717 _104718 f g)). Qed.
Lemma lem4369407 {_104717 _104718 : Type'} (f : type686 _104717) : (term1025 _104717 _104718 f) = (term966 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369406 _104717 _104718 f g)). Qed.
Lemma lem4369408 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369409 {_104717 _104718 : Type'} (f : type686 _104717) : (term1026 _104717 _104718 f) = (term967 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369408 _104718) (@lem4369407 _104717 _104718 f)). Qed.
Lemma lem4369410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369411 {_104717 _104718 : Type'} (f : type686 _104717) : (term1027 _104717 _104718 f) = (term1016 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369410) (@lem4369409 _104717 _104718 f)). Qed.
Lemma lem4369412 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1028 _104717 _104718 f g) = (term998 _104717 _104718 f g).
Proof. exact (eq_refl (term1028 _104717 _104718 f g)). Qed.
Lemma lem4369413 {_104717 _104718 : Type'} (f : type686 _104717) : (term1029 _104717 _104718 f) = (term999 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369412 _104717 _104718 f g)). Qed.
Lemma lem4369414 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369415 {_104717 _104718 : Type'} (f : type686 _104717) : (term1030 _104717 _104718 f) = (term1000 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369414 _104718) (@lem4369413 _104717 _104718 f)). Qed.
Lemma lem4369416 {_104717 _104718 : Type'} (f : type686 _104717) : (term1022 _104717 _104718 f) = (term1018 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369411 _104717 _104718 f) (@lem4369415 _104717 _104718 f)). Qed.
Lemma lem4369417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369418 {_104717 _104718 : Type'} (f : type686 _104717) : (term1031 _104717 _104718 f) = (term1032 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369417) (@lem4369416 _104717 _104718 f)). Qed.
Lemma lem4369419 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1024 _104717 _104718 f g) = (term965 _104717 _104718 f g).
Proof. exact (eq_refl (term1024 _104717 _104718 f g)). Qed.
Lemma lem4369420 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369421 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1033 _104717 _104718 f g) = (term1034 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369420) (@lem4369419 _104717 _104718 f g)). Qed.
Lemma lem4369422 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1028 _104717 _104718 f g) = (term998 _104717 _104718 f g).
Proof. exact (eq_refl (term1028 _104717 _104718 f g)). Qed.
Lemma lem4369423 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1035 _104717 _104718 f g) = (term1036 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369421 _104717 _104718 f g) (@lem4369422 _104717 _104718 f g)). Qed.
Lemma lem4369424 {_104717 _104718 : Type'} (f : type686 _104717) : (term1037 _104717 _104718 f) = (term1038 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369423 _104717 _104718 f g)). Qed.
Lemma lem4369425 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369426 {_104717 _104718 : Type'} (f : type686 _104717) : (term1023 _104717 _104718 f) = (term1039 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369425 _104718) (@lem4369424 _104717 _104718 f)). Qed.
Lemma lem4369427 {_104717 _104718 : Type'} (f : type686 _104717) : ((term1022 _104717 _104718 f) = (term1023 _104717 _104718 f)) = ((term1018 _104717 _104718 f) = (term1039 _104717 _104718 f)).
Proof. exact (MK_COMB (@lem4369418 _104717 _104718 f) (@lem4369426 _104717 _104718 f)). Qed.
Lemma lem4369428 {_104717 _104718 : Type'} (f : type686 _104717) : (term1018 _104717 _104718 f) = (term1039 _104717 _104718 f).
Proof. exact (EQ_MP (@lem4369427 _104717 _104718 f) (@lem4369405 _104717 _104718 f)). Qed.
Lemma lem4369430 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369431 {_104717 : Type'} (P : _104717 -> Prop) (Q : _104717 -> Prop) : (term629 _104717 P Q) = (term628 _104717 P Q).
Proof. exact (@lem4369430 _104717 P Q). Qed.
Lemma lem4369432 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1040 _104717 _104718 f g) = (term1041 _104717 _104718 f g).
Proof. exact (@lem4369431 _104717 (term964 _104717 _104718 f g) (term997 _104717 _104718 f g)). Qed.
Lemma lem4369433 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1042 _104717 _104718 f g p1) = (term963 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1042 _104717 _104718 f g p1)). Qed.
Lemma lem4369434 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1043 _104717 _104718 f g) = (term964 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369433 _104717 _104718 f g p1)). Qed.
Lemma lem4369435 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369436 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1044 _104717 _104718 f g) = (term965 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369435 _104717) (@lem4369434 _104717 _104718 f g)). Qed.
Lemma lem4369437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369438 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1045 _104717 _104718 f g) = (term1034 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369437) (@lem4369436 _104717 _104718 f g)). Qed.
Lemma lem4369439 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1046 _104717 _104718 f g p1) = (term996 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1046 _104717 _104718 f g p1)). Qed.
Lemma lem4369440 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1047 _104717 _104718 f g) = (term997 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369439 _104717 _104718 f g p1)). Qed.
Lemma lem4369441 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369442 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1048 _104717 _104718 f g) = (term998 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369441 _104717) (@lem4369440 _104717 _104718 f g)). Qed.
Lemma lem4369443 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1040 _104717 _104718 f g) = (term1036 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369438 _104717 _104718 f g) (@lem4369442 _104717 _104718 f g)). Qed.
Lemma lem4369444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369445 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1049 _104717 _104718 f g) = (term1050 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369444) (@lem4369443 _104717 _104718 f g)). Qed.
Lemma lem4369446 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1042 _104717 _104718 f g p1) = (term963 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1042 _104717 _104718 f g p1)). Qed.
Lemma lem4369447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369448 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1051 _104717 _104718 f g p1) = (term1052 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369447) (@lem4369446 _104717 _104718 f g p1)). Qed.
Lemma lem4369449 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1046 _104717 _104718 f g p1) = (term996 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1046 _104717 _104718 f g p1)). Qed.
Lemma lem4369450 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1053 _104717 _104718 f g p1) = (term1054 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369448 _104717 _104718 f g p1) (@lem4369449 _104717 _104718 f g p1)). Qed.
Lemma lem4369451 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1055 _104717 _104718 f g) = (term1056 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369450 _104717 _104718 f g p1)). Qed.
Lemma lem4369452 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369453 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1041 _104717 _104718 f g) = (term1057 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369452 _104717) (@lem4369451 _104717 _104718 f g)). Qed.
Lemma lem4369454 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term1040 _104717 _104718 f g) = (term1041 _104717 _104718 f g)) = ((term1036 _104717 _104718 f g) = (term1057 _104717 _104718 f g)).
Proof. exact (MK_COMB (@lem4369445 _104717 _104718 f g) (@lem4369453 _104717 _104718 f g)). Qed.
Lemma lem4369455 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1036 _104717 _104718 f g) = (term1057 _104717 _104718 f g).
Proof. exact (EQ_MP (@lem4369454 _104717 _104718 f g) (@lem4369432 _104717 _104718 f g)). Qed.
Lemma lem4369457 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369458 {_104718 : Type'} (P : _104718 -> Prop) (Q : _104718 -> Prop) : (term629 _104718 P Q) = (term628 _104718 P Q).
Proof. exact (@lem4369457 _104718 P Q). Qed.
Lemma lem4369459 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1058 _104717 _104718 f g p1) = (term1059 _104717 _104718 f g p1).
Proof. exact (@lem4369458 _104718 (term962 _104717 _104718 f g p1) (term995 _104717 _104718 f g p1)). Qed.
Lemma lem4369460 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1060 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1060 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369461 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1061 _104717 _104718 f g p1) = (term962 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369460 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369462 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369463 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1062 _104717 _104718 f g p1) = (term963 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369462 _104718) (@lem4369461 _104717 _104718 f g p1)). Qed.
Lemma lem4369464 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369465 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1063 _104717 _104718 f g p1) = (term1052 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369464) (@lem4369463 _104717 _104718 f g p1)). Qed.
Lemma lem4369466 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1064 _104717 _104718 f g p1 p2) = (term994 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1064 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369467 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1065 _104717 _104718 f g p1) = (term995 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369466 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369468 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369469 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1066 _104717 _104718 f g p1) = (term996 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369468 _104718) (@lem4369467 _104717 _104718 f g p1)). Qed.
Lemma lem4369470 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1058 _104717 _104718 f g p1) = (term1054 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369465 _104717 _104718 f g p1) (@lem4369469 _104717 _104718 f g p1)). Qed.
Lemma lem4369471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369472 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1067 _104717 _104718 f g p1) = (term1068 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369471) (@lem4369470 _104717 _104718 f g p1)). Qed.
Lemma lem4369473 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1060 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1060 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369474 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369475 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1069 _104717 _104718 f g p1 p2) = (term1070 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369474) (@lem4369473 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369476 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1064 _104717 _104718 f g p1 p2) = (term994 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1064 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369477 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1071 _104717 _104718 f g p1 p2) = (term1072 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369475 _104717 _104718 f g p1 p2) (@lem4369476 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369478 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1073 _104717 _104718 f g p1) = (term1074 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369477 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369479 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369480 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1059 _104717 _104718 f g p1) = (term1075 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369479 _104718) (@lem4369478 _104717 _104718 f g p1)). Qed.
Lemma lem4369481 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : ((term1058 _104717 _104718 f g p1) = (term1059 _104717 _104718 f g p1)) = ((term1054 _104717 _104718 f g p1) = (term1075 _104717 _104718 f g p1)).
Proof. exact (MK_COMB (@lem4369472 _104717 _104718 f g p1) (@lem4369480 _104717 _104718 f g p1)). Qed.
Lemma lem4369482 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1054 _104717 _104718 f g p1) = (term1075 _104717 _104718 f g p1).
Proof. exact (EQ_MP (@lem4369481 _104717 _104718 f g p1) (@lem4369459 _104717 _104718 f g p1)). Qed.
Lemma lem4369484 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369485 {_104717 : Type'} (P : type686 _104717) (Q : type686 _104717) : (term786 _104717 P Q) = (term785 _104717 P Q).
Proof. exact (@lem4369484 (_104717 -> Prop) P Q). Qed.
Lemma lem4369486 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1076 _104717 _104718 f g p1 p2) = (term1077 _104717 _104718 f g p1 p2).
Proof. exact (@lem4369485 _104717 (term960 _104717 _104718 f g p1 p2) (term993 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369487 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1078 _104717 _104718 f g p1 p2 t) = (term959 _104717 _104718 t f g p1 p2).
Proof. exact (eq_refl (term1078 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4369488 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1079 _104717 _104718 f g p1 p2) = (term960 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369487 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369489 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369490 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1080 _104717 _104718 f g p1 p2) = (term961 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369489 _104717) (@lem4369488 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369491 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369492 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1081 _104717 _104718 f g p1 p2) = (term1070 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369491) (@lem4369490 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369493 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1082 _104717 _104718 f g p1 p2 t) = (term992 _104717 _104718 f g t p1 p2).
Proof. exact (eq_refl (term1082 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4369494 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1083 _104717 _104718 f g p1 p2) = (term993 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369493 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369495 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369496 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1084 _104717 _104718 f g p1 p2) = (term994 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369495 _104717) (@lem4369494 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369497 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1076 _104717 _104718 f g p1 p2) = (term1072 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369492 _104717 _104718 f g p1 p2) (@lem4369496 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369499 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1085 _104717 _104718 f g p1 p2) = (term1086 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369498) (@lem4369497 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369500 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1078 _104717 _104718 f g p1 p2 t) = (term959 _104717 _104718 t f g p1 p2).
Proof. exact (eq_refl (term1078 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4369501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369502 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1087 _104717 _104718 f g p1 p2 t) = (term1088 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369501) (@lem4369500 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369503 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1082 _104717 _104718 f g p1 p2 t) = (term992 _104717 _104718 f g t p1 p2).
Proof. exact (eq_refl (term1082 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4369504 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1089 _104717 _104718 f g p1 p2 t) = (term1090 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4369502 _104717 _104718 t f g p1 p2) (@lem4369503 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369505 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1091 _104717 _104718 f g p1 p2) = (term1092 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369504 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369506 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369507 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1077 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369506 _104717) (@lem4369505 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369508 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1076 _104717 _104718 f g p1 p2) = (term1077 _104717 _104718 f g p1 p2)) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)).
Proof. exact (MK_COMB (@lem4369499 _104717 _104718 f g p1 p2) (@lem4369507 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369509 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2).
Proof. exact (EQ_MP (@lem4369508 _104717 _104718 f g p1 p2) (@lem4369486 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369512 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1094 _104717 _104718 f g p1 p2) = (term1094 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1094 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369513 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1094 _104717 _104718 f g p1 p2) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)).
Proof. exact (eq_refl (term1094 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369514 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1095 _104717 _104718 f g p1 p2) = (term1095 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1095 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369515 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1094 _104717 _104718 f g p1 p2) = (term1094 _104717 _104718 f g p1 p2)) = ((term1094 _104717 _104718 f g p1 p2) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2))).
Proof. exact (MK_COMB (@lem4369514 _104717 _104718 f g p1 p2) (@lem4369513 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369516 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1094 _104717 _104718 f g p1 p2) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)).
Proof. exact (eq_refl (term1094 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369518 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1095 _104717 _104718 f g p1 p2) = (term1096 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369517) (@lem4369516 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369519 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)).
Proof. exact (eq_refl ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2))). Qed.
Lemma lem4369520 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1094 _104717 _104718 f g p1 p2) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2))) = (((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2))).
Proof. exact (MK_COMB (@lem4369518 _104717 _104718 f g p1 p2) (@lem4369519 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369521 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1094 _104717 _104718 f g p1 p2) = (term1094 _104717 _104718 f g p1 p2)) = (((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2))).
Proof. exact (TRANS (@lem4369515 _104717 _104718 f g p1 p2) (@lem4369520 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369522 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)) = ((term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2)).
Proof. exact (EQ_MP (@lem4369521 _104717 _104718 f g p1 p2) (@lem4369512 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369523 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1072 _104717 _104718 f g p1 p2) = (term1093 _104717 _104718 f g p1 p2).
Proof. exact (EQ_MP (@lem4369522 _104717 _104718 f g p1 p2) (@lem4369509 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369525 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369526 {_104718 : Type'} (P : type686 _104718) (Q : type686 _104718) : (term786 _104718 P Q) = (term785 _104718 P Q).
Proof. exact (@lem4369525 (_104718 -> Prop) P Q). Qed.
Lemma lem4369527 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1097 _104717 _104718 f g t p1 p2) = (term1098 _104717 _104718 f g t p1 p2).
Proof. exact (@lem4369526 _104718 (term958 _104717 _104718 t f g p1 p2) (term991 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369528 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1099 _104717 _104718 t f g p1 p2 t') = (term956 _104717 _104718 t t' f g p1 p2).
Proof. exact (eq_refl (term1099 _104717 _104718 t f g p1 p2 t')). Qed.
Lemma lem4369529 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1100 _104717 _104718 t f g p1 p2) = (term958 _104717 _104718 t f g p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369528 _104717 _104718 t t' f g p1 p2)). Qed.
Lemma lem4369530 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369531 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1101 _104717 _104718 t f g p1 p2) = (term959 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369530 _104718) (@lem4369529 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369532 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369533 {_104717 _104718 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1102 _104717 _104718 t f g p1 p2) = (term1088 _104717 _104718 t f g p1 p2).
Proof. exact (MK_COMB (@lem4369532) (@lem4369531 _104717 _104718 t f g p1 p2)). Qed.
Lemma lem4369534 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1103 _104717 _104718 f g t p1 p2 t') = (term989 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1103 _104717 _104718 f g t p1 p2 t')). Qed.
Lemma lem4369535 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1104 _104717 _104718 f g t p1 p2) = (term991 _104717 _104718 f g t p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369534 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4369536 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369537 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1105 _104717 _104718 f g t p1 p2) = (term992 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4369536 _104718) (@lem4369535 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369538 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1097 _104717 _104718 f g t p1 p2) = (term1090 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4369533 _104717 _104718 t f g p1 p2) (@lem4369537 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369539 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369540 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1106 _104717 _104718 f g t p1 p2) = (term1107 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4369539) (@lem4369538 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369541 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1099 _104717 _104718 t f g p1 p2 t') = (term956 _104717 _104718 t t' f g p1 p2).
Proof. exact (eq_refl (term1099 _104717 _104718 t f g p1 p2 t')). Qed.
Lemma lem4369542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369543 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1108 _104717 _104718 t f g p1 p2 t') = (term1109 _104717 _104718 t t' f g p1 p2).
Proof. exact (MK_COMB (@lem4369542) (@lem4369541 _104717 _104718 t t' f g p1 p2)). Qed.
Lemma lem4369544 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1103 _104717 _104718 f g t p1 p2 t') = (term989 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1103 _104717 _104718 f g t p1 p2 t')). Qed.
Lemma lem4369545 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1110 _104717 _104718 f g t p1 p2 t') = (term1111 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4369543 _104717 _104718 t t' f g p1 p2) (@lem4369544 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4369546 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1112 _104717 _104718 f g t p1 p2) = (term1113 _104717 _104718 f g t p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4369545 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4369547 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4369548 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1098 _104717 _104718 f g t p1 p2) = (term1114 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4369547 _104718) (@lem4369546 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369549 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : ((term1097 _104717 _104718 f g t p1 p2) = (term1098 _104717 _104718 f g t p1 p2)) = ((term1090 _104717 _104718 f g t p1 p2) = (term1114 _104717 _104718 f g t p1 p2)).
Proof. exact (MK_COMB (@lem4369540 _104717 _104718 f g t p1 p2) (@lem4369548 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369550 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1090 _104717 _104718 f g t p1 p2) = (term1114 _104717 _104718 f g t p1 p2).
Proof. exact (EQ_MP (@lem4369549 _104717 _104718 f g t p1 p2) (@lem4369527 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369551 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1092 _104717 _104718 f g p1 p2) = (term1115 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4369550 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4369552 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4369553 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1093 _104717 _104718 f g p1 p2) = (term1116 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4369552 _104717) (@lem4369551 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369554 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1072 _104717 _104718 f g p1 p2) = (term1116 _104717 _104718 f g p1 p2).
Proof. exact (TRANS (@lem4369523 _104717 _104718 f g p1 p2) (@lem4369553 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369555 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1074 _104717 _104718 f g p1) = (term1117 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4369554 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4369556 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4369557 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1075 _104717 _104718 f g p1) = (term1118 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4369556 _104718) (@lem4369555 _104717 _104718 f g p1)). Qed.
Lemma lem4369558 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1054 _104717 _104718 f g p1) = (term1118 _104717 _104718 f g p1).
Proof. exact (TRANS (@lem4369482 _104717 _104718 f g p1) (@lem4369557 _104717 _104718 f g p1)). Qed.
Lemma lem4369559 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1056 _104717 _104718 f g) = (term1119 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4369558 _104717 _104718 f g p1)). Qed.
Lemma lem4369560 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4369561 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1057 _104717 _104718 f g) = (term1120 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4369560 _104717) (@lem4369559 _104717 _104718 f g)). Qed.
Lemma lem4369562 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1036 _104717 _104718 f g) = (term1120 _104717 _104718 f g).
Proof. exact (TRANS (@lem4369455 _104717 _104718 f g) (@lem4369561 _104717 _104718 f g)). Qed.
Lemma lem4369563 {_104717 _104718 : Type'} (f : type686 _104717) : (term1038 _104717 _104718 f) = (term1121 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4369562 _104717 _104718 f g)). Qed.
Lemma lem4369564 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4369565 {_104717 _104718 : Type'} (f : type686 _104717) : (term1039 _104717 _104718 f) = (term1122 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4369564 _104718) (@lem4369563 _104717 _104718 f)). Qed.
Lemma lem4369566 {_104717 _104718 : Type'} (f : type686 _104717) : (term1018 _104717 _104718 f) = (term1122 _104717 _104718 f).
Proof. exact (TRANS (@lem4369428 _104717 _104718 f) (@lem4369565 _104717 _104718 f)). Qed.
Lemma lem4369567 {_104717 _104718 : Type'} : (term1020 _104717 _104718) = (term1123 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4369566 _104717 _104718 f)). Qed.
Lemma lem4369568 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4369569 {_104717 _104718 : Type'} : (term1021 _104717 _104718) = (term1124 _104717 _104718).
Proof. exact (MK_COMB (@lem4369568 _104717) (@lem4369567 _104717 _104718)). Qed.
Lemma lem4369570 {_104717 _104718 : Type'} : (term1003 _104717 _104718) = (term1124 _104717 _104718).
Proof. exact (TRANS (@lem4369401 _104717 _104718) (@lem4369569 _104717 _104718)). Qed.
Lemma lem4369571 {_104717 _104718 : Type'} : (term717 _104717 _104718) = (term1124 _104717 _104718).
Proof. exact (TRANS (@lem4369374 _104717 _104718) (@lem4369570 _104717 _104718)). Qed.
Lemma lem4369572 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369573 {_104717 _104718 : Type'} : (term718 _104717 _104718) = (term1125 _104717 _104718).
Proof. exact (MK_COMB (@lem4369572) (@lem4369571 _104717 _104718)). Qed.
Lemma lem4369575 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369576 {_104758 : Type'} (P : Prop) (Q : type686 _104758) : (term915 _104758 P Q) = (term916 _104758 P Q).
Proof. exact (@lem4369575 (_104758 -> Prop) P Q). Qed.
Lemma lem4369577 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1126 _104757 _104758 s p1 f p2) = (term1127 _104757 _104758 s p1 f p2).
Proof. exact (@lem4369576 _104758 (s p1) (term363 _104758 f p2)). Qed.
Lemma lem4369578 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term431 _104758 f p2 t) = (term361 _104758 f t p2).
Proof. exact (eq_refl (term431 _104758 f p2 t)). Qed.
Lemma lem4369579 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term902 _104758 f p2) = (term363 _104758 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369578 _104758 f t p2)). Qed.
Lemma lem4369580 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369581 {_104758 : Type'} (f : type686 _104758) (p2 : _104758) : (term903 _104758 f p2) = (term364 _104758 f p2).
Proof. exact (MK_COMB (@lem4369580 _104758) (@lem4369579 _104758 f p2)). Qed.
Lemma lem4369582 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term372 _104757 s p1) = (term372 _104757 s p1).
Proof. exact (eq_refl (term372 _104757 s p1)). Qed.
Lemma lem4369583 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1126 _104757 _104758 s p1 f p2) = (term388 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369582 _104757 s p1) (@lem4369581 _104758 f p2)). Qed.
Lemma lem4369584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369585 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1128 _104757 _104758 s p1 f p2) = (term389 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369584) (@lem4369583 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369586 {_104758 : Type'} (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term431 _104758 f p2 t) = (term361 _104758 f t p2).
Proof. exact (eq_refl (term431 _104758 f p2 t)). Qed.
Lemma lem4369587 {_104757 : Type'} (s : _104757 -> Prop) (p1 : _104757) : (term372 _104757 s p1) = (term372 _104757 s p1).
Proof. exact (eq_refl (term372 _104757 s p1)). Qed.
Lemma lem4369588 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term1129 _104757 _104758 s p1 f p2 t) = (term1130 _104757 _104758 s p1 f t p2).
Proof. exact (MK_COMB (@lem4369587 _104757 s p1) (@lem4369586 _104758 f t p2)). Qed.
Lemma lem4369589 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1131 _104757 _104758 s p1 f p2) = (term1132 _104757 _104758 s p1 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369588 _104757 _104758 s p1 f t p2)). Qed.
Lemma lem4369590 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369591 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1127 _104757 _104758 s p1 f p2) = (term1133 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369590 _104758) (@lem4369589 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369592 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : ((term1126 _104757 _104758 s p1 f p2) = (term1127 _104757 _104758 s p1 f p2)) = ((term388 _104757 _104758 s p1 f p2) = (term1133 _104757 _104758 s p1 f p2)).
Proof. exact (MK_COMB (@lem4369585 _104757 _104758 s p1 f p2) (@lem4369591 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369593 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term388 _104757 _104758 s p1 f p2) = (term1133 _104757 _104758 s p1 f p2).
Proof. exact (EQ_MP (@lem4369592 _104757 _104758 s p1 f p2) (@lem4369577 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369594 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369595 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term527 _104757 _104758 s p1 f p2) = (term1134 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369594) (@lem4369593 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369596 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term522 _104757 _104758 f s p1 p2) = (term522 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term522 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369597 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term529 _104757 _104758 f s p1 p2) = (term1135 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369595 _104757 _104758 s p1 f p2) (@lem4369596 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369599 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369600 {_104758 : Type'} (P : type686 _104758) (Q : Prop) : (term898 _104758 P Q) = (term899 _104758 P Q).
Proof. exact (@lem4369599 (_104758 -> Prop) P Q). Qed.
Lemma lem4369601 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1136 _104757 _104758 f s p1 p2) = (term1137 _104757 _104758 f s p1 p2).
Proof. exact (@lem4369600 _104758 (term1132 _104757 _104758 s p1 f p2) (term522 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369602 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term1138 _104757 _104758 s p1 f p2 t) = (term1130 _104757 _104758 s p1 f t p2).
Proof. exact (eq_refl (term1138 _104757 _104758 s p1 f p2 t)). Qed.
Lemma lem4369603 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1139 _104757 _104758 s p1 f p2) = (term1132 _104757 _104758 s p1 f p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369602 _104757 _104758 s p1 f t p2)). Qed.
Lemma lem4369604 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369605 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1140 _104757 _104758 s p1 f p2) = (term1133 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369604 _104758) (@lem4369603 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369606 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369607 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term1141 _104757 _104758 s p1 f p2) = (term1134 _104757 _104758 s p1 f p2).
Proof. exact (MK_COMB (@lem4369606) (@lem4369605 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369608 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term522 _104757 _104758 f s p1 p2) = (term522 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term522 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369609 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1136 _104757 _104758 f s p1 p2) = (term1135 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369607 _104757 _104758 s p1 f p2) (@lem4369608 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369611 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1142 _104757 _104758 f s p1 p2) = (term1143 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369610) (@lem4369609 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369612 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term1138 _104757 _104758 s p1 f p2 t) = (term1130 _104757 _104758 s p1 f t p2).
Proof. exact (eq_refl (term1138 _104757 _104758 s p1 f p2 t)). Qed.
Lemma lem4369613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369614 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (t : _104758 -> Prop) (p2 : _104758) : (term1144 _104757 _104758 s p1 f p2 t) = (term1145 _104757 _104758 s p1 f t p2).
Proof. exact (MK_COMB (@lem4369613) (@lem4369612 _104757 _104758 s p1 f t p2)). Qed.
Lemma lem4369615 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term522 _104757 _104758 f s p1 p2) = (term522 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term522 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369616 {_104757 _104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1146 _104757 _104758 t f s p1 p2) = (term1147 _104757 _104758 t f s p1 p2).
Proof. exact (MK_COMB (@lem4369614 _104757 _104758 s p1 f t p2) (@lem4369615 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369617 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1148 _104757 _104758 f s p1 p2) = (term1149 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369616 _104757 _104758 t f s p1 p2)). Qed.
Lemma lem4369618 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369619 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1137 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369618 _104758) (@lem4369617 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369620 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term1136 _104757 _104758 f s p1 p2) = (term1137 _104757 _104758 f s p1 p2)) = ((term1135 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2)).
Proof. exact (MK_COMB (@lem4369611 _104757 _104758 f s p1 p2) (@lem4369619 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369621 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1135 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (EQ_MP (@lem4369620 _104757 _104758 f s p1 p2) (@lem4369601 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369622 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term529 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (TRANS (@lem4369597 _104757 _104758 f s p1 p2) (@lem4369621 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369623 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term721 _104757 _104758 f s p1) = (term1151 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369622 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369624 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369625 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term732 _104757 _104758 f s p1) = (term1152 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369624 _104758) (@lem4369623 _104757 _104758 f s p1)). Qed.
Lemma lem4369626 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term743 _104757 _104758 f s) = (term1153 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369625 _104757 _104758 f s p1)). Qed.
Lemma lem4369627 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369628 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term754 _104757 _104758 f s) = (term1154 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369627 _104757) (@lem4369626 _104757 _104758 f s)). Qed.
Lemma lem4369629 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term765 _104757 _104758 s) = (term1155 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369628 _104757 _104758 f s)). Qed.
Lemma lem4369630 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369631 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term776 _104757 _104758 s) = (term1156 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369630 _104758) (@lem4369629 _104757 _104758 s)). Qed.
Lemma lem4369632 {_104757 _104758 : Type'} : (term789 _104757 _104758) = (term1157 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369631 _104757 _104758 s)). Qed.
Lemma lem4369633 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369634 {_104757 _104758 : Type'} : (term800 _104757 _104758) = (term1158 _104757 _104758).
Proof. exact (MK_COMB (@lem4369633 _104757) (@lem4369632 _104757 _104758)). Qed.
Lemma lem4369635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369636 {_104757 _104758 : Type'} : (term802 _104757 _104758) = (term1159 _104757 _104758).
Proof. exact (MK_COMB (@lem4369635) (@lem4369634 _104757 _104758)). Qed.
Lemma lem4369638 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369639 {_104758 : Type'} (P : Prop) (Q : type686 _104758) : (term915 _104758 P Q) = (term916 _104758 P Q).
Proof. exact (@lem4369638 (_104758 -> Prop) P Q). Qed.
Lemma lem4369640 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1160 _104757 _104758 f s p1 p2) = (term1161 _104757 _104758 f s p1 p2).
Proof. exact (@lem4369639 _104758 (term510 _104757 _104758 s p1 f p2) (term391 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369641 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term518 _104757 _104758 f s p1 p2 t) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term518 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369642 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1162 _104757 _104758 f s p1 p2) = (term391 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369641 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369643 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369644 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1163 _104757 _104758 f s p1 p2) = (term392 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369643 _104758) (@lem4369642 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369645 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term524 _104757 _104758 s p1 f p2) = (term524 _104757 _104758 s p1 f p2).
Proof. exact (eq_refl (term524 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369646 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1160 _104757 _104758 f s p1 p2) = (term526 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369645 _104757 _104758 s p1 f p2) (@lem4369644 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369648 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1164 _104757 _104758 f s p1 p2) = (term1165 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369647) (@lem4369646 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369649 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term518 _104757 _104758 f s p1 p2 t) = (term390 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term518 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369650 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1 : _104757) (f : type686 _104758) (p2 : _104758) : (term524 _104757 _104758 s p1 f p2) = (term524 _104757 _104758 s p1 f p2).
Proof. exact (eq_refl (term524 _104757 _104758 s p1 f p2)). Qed.
Lemma lem4369651 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1166 _104757 _104758 f s p1 p2 t) = (term1167 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4369650 _104757 _104758 s p1 f p2) (@lem4369649 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369652 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1168 _104757 _104758 f s p1 p2) = (term1169 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369651 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369653 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369654 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1161 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369653 _104758) (@lem4369652 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369655 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term1160 _104757 _104758 f s p1 p2) = (term1161 _104757 _104758 f s p1 p2)) = ((term526 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2)).
Proof. exact (MK_COMB (@lem4369648 _104757 _104758 f s p1 p2) (@lem4369654 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369656 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term526 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2).
Proof. exact (EQ_MP (@lem4369655 _104757 _104758 f s p1 p2) (@lem4369640 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369657 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term722 _104757 _104758 f s p1) = (term1171 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369656 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369658 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369659 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term737 _104757 _104758 f s p1) = (term1172 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369658 _104758) (@lem4369657 _104757 _104758 f s p1)). Qed.
Lemma lem4369660 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term744 _104757 _104758 f s) = (term1173 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369659 _104757 _104758 f s p1)). Qed.
Lemma lem4369661 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369662 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term759 _104757 _104758 f s) = (term1174 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369661 _104757) (@lem4369660 _104757 _104758 f s)). Qed.
Lemma lem4369663 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term766 _104757 _104758 s) = (term1175 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369662 _104757 _104758 f s)). Qed.
Lemma lem4369664 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369665 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term781 _104757 _104758 s) = (term1176 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369664 _104758) (@lem4369663 _104757 _104758 s)). Qed.
Lemma lem4369666 {_104757 _104758 : Type'} : (term790 _104757 _104758) = (term1177 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369665 _104757 _104758 s)). Qed.
Lemma lem4369667 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369668 {_104757 _104758 : Type'} : (term805 _104757 _104758) = (term1178 _104757 _104758).
Proof. exact (MK_COMB (@lem4369667 _104757) (@lem4369666 _104757 _104758)). Qed.
Lemma lem4369669 {_104757 _104758 : Type'} : (term806 _104757 _104758) = (term1179 _104757 _104758).
Proof. exact (MK_COMB (@lem4369636 _104757 _104758) (@lem4369668 _104757 _104758)). Qed.
Lemma lem4369671 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369672 {_104757 : Type'} (P : type686 _104757) (Q : type686 _104757) : (term786 _104757 P Q) = (term785 _104757 P Q).
Proof. exact (@lem4369671 (_104757 -> Prop) P Q). Qed.
Lemma lem4369673 {_104757 _104758 : Type'} : (term1180 _104757 _104758) = (term1181 _104757 _104758).
Proof. exact (@lem4369672 _104757 (term1157 _104757 _104758) (term1177 _104757 _104758)). Qed.
Lemma lem4369674 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1182 _104757 _104758 s) = (term1156 _104757 _104758 s).
Proof. exact (eq_refl (term1182 _104757 _104758 s)). Qed.
Lemma lem4369675 {_104757 _104758 : Type'} : (term1183 _104757 _104758) = (term1157 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369674 _104757 _104758 s)). Qed.
Lemma lem4369676 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369677 {_104757 _104758 : Type'} : (term1184 _104757 _104758) = (term1158 _104757 _104758).
Proof. exact (MK_COMB (@lem4369676 _104757) (@lem4369675 _104757 _104758)). Qed.
Lemma lem4369678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369679 {_104757 _104758 : Type'} : (term1185 _104757 _104758) = (term1159 _104757 _104758).
Proof. exact (MK_COMB (@lem4369678) (@lem4369677 _104757 _104758)). Qed.
Lemma lem4369680 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1186 _104757 _104758 s) = (term1176 _104757 _104758 s).
Proof. exact (eq_refl (term1186 _104757 _104758 s)). Qed.
Lemma lem4369681 {_104757 _104758 : Type'} : (term1187 _104757 _104758) = (term1177 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369680 _104757 _104758 s)). Qed.
Lemma lem4369682 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369683 {_104757 _104758 : Type'} : (term1188 _104757 _104758) = (term1178 _104757 _104758).
Proof. exact (MK_COMB (@lem4369682 _104757) (@lem4369681 _104757 _104758)). Qed.
Lemma lem4369684 {_104757 _104758 : Type'} : (term1180 _104757 _104758) = (term1179 _104757 _104758).
Proof. exact (MK_COMB (@lem4369679 _104757 _104758) (@lem4369683 _104757 _104758)). Qed.
Lemma lem4369685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369686 {_104757 _104758 : Type'} : (term1189 _104757 _104758) = (term1190 _104757 _104758).
Proof. exact (MK_COMB (@lem4369685) (@lem4369684 _104757 _104758)). Qed.
Lemma lem4369687 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1182 _104757 _104758 s) = (term1156 _104757 _104758 s).
Proof. exact (eq_refl (term1182 _104757 _104758 s)). Qed.
Lemma lem4369688 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369689 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1191 _104757 _104758 s) = (term1192 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369688) (@lem4369687 _104757 _104758 s)). Qed.
Lemma lem4369690 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1186 _104757 _104758 s) = (term1176 _104757 _104758 s).
Proof. exact (eq_refl (term1186 _104757 _104758 s)). Qed.
Lemma lem4369691 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1193 _104757 _104758 s) = (term1194 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369689 _104757 _104758 s) (@lem4369690 _104757 _104758 s)). Qed.
Lemma lem4369692 {_104757 _104758 : Type'} : (term1195 _104757 _104758) = (term1196 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369691 _104757 _104758 s)). Qed.
Lemma lem4369693 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369694 {_104757 _104758 : Type'} : (term1181 _104757 _104758) = (term1197 _104757 _104758).
Proof. exact (MK_COMB (@lem4369693 _104757) (@lem4369692 _104757 _104758)). Qed.
Lemma lem4369695 {_104757 _104758 : Type'} : ((term1180 _104757 _104758) = (term1181 _104757 _104758)) = ((term1179 _104757 _104758) = (term1197 _104757 _104758)).
Proof. exact (MK_COMB (@lem4369686 _104757 _104758) (@lem4369694 _104757 _104758)). Qed.
Lemma lem4369696 {_104757 _104758 : Type'} : (term1179 _104757 _104758) = (term1197 _104757 _104758).
Proof. exact (EQ_MP (@lem4369695 _104757 _104758) (@lem4369673 _104757 _104758)). Qed.
Lemma lem4369698 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369699 {_104758 : Type'} (P : type180 _104758) (Q : type180 _104758) : (term675 _104758 P Q) = (term674 _104758 P Q).
Proof. exact (@lem4369698 (type686 _104758) P Q). Qed.
Lemma lem4369700 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1198 _104757 _104758 s) = (term1199 _104757 _104758 s).
Proof. exact (@lem4369699 _104758 (term1155 _104757 _104758 s) (term1175 _104757 _104758 s)). Qed.
Lemma lem4369701 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1200 _104757 _104758 s f) = (term1154 _104757 _104758 f s).
Proof. exact (eq_refl (term1200 _104757 _104758 s f)). Qed.
Lemma lem4369702 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1201 _104757 _104758 s) = (term1155 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369701 _104757 _104758 f s)). Qed.
Lemma lem4369703 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369704 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1202 _104757 _104758 s) = (term1156 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369703 _104758) (@lem4369702 _104757 _104758 s)). Qed.
Lemma lem4369705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369706 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1203 _104757 _104758 s) = (term1192 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369705) (@lem4369704 _104757 _104758 s)). Qed.
Lemma lem4369707 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1204 _104757 _104758 s f) = (term1174 _104757 _104758 f s).
Proof. exact (eq_refl (term1204 _104757 _104758 s f)). Qed.
Lemma lem4369708 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1205 _104757 _104758 s) = (term1175 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369707 _104757 _104758 f s)). Qed.
Lemma lem4369709 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369710 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1206 _104757 _104758 s) = (term1176 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369709 _104758) (@lem4369708 _104757 _104758 s)). Qed.
Lemma lem4369711 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1198 _104757 _104758 s) = (term1194 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369706 _104757 _104758 s) (@lem4369710 _104757 _104758 s)). Qed.
Lemma lem4369712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369713 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1207 _104757 _104758 s) = (term1208 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369712) (@lem4369711 _104757 _104758 s)). Qed.
Lemma lem4369714 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1200 _104757 _104758 s f) = (term1154 _104757 _104758 f s).
Proof. exact (eq_refl (term1200 _104757 _104758 s f)). Qed.
Lemma lem4369715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369716 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1209 _104757 _104758 s f) = (term1210 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369715) (@lem4369714 _104757 _104758 f s)). Qed.
Lemma lem4369717 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1204 _104757 _104758 s f) = (term1174 _104757 _104758 f s).
Proof. exact (eq_refl (term1204 _104757 _104758 s f)). Qed.
Lemma lem4369718 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1211 _104757 _104758 s f) = (term1212 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369716 _104757 _104758 f s) (@lem4369717 _104757 _104758 f s)). Qed.
Lemma lem4369719 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1213 _104757 _104758 s) = (term1214 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369718 _104757 _104758 f s)). Qed.
Lemma lem4369720 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369721 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1199 _104757 _104758 s) = (term1215 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369720 _104758) (@lem4369719 _104757 _104758 s)). Qed.
Lemma lem4369722 {_104757 _104758 : Type'} (s : _104757 -> Prop) : ((term1198 _104757 _104758 s) = (term1199 _104757 _104758 s)) = ((term1194 _104757 _104758 s) = (term1215 _104757 _104758 s)).
Proof. exact (MK_COMB (@lem4369713 _104757 _104758 s) (@lem4369721 _104757 _104758 s)). Qed.
Lemma lem4369723 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1194 _104757 _104758 s) = (term1215 _104757 _104758 s).
Proof. exact (EQ_MP (@lem4369722 _104757 _104758 s) (@lem4369700 _104757 _104758 s)). Qed.
Lemma lem4369725 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369726 {_104757 : Type'} (P : _104757 -> Prop) (Q : _104757 -> Prop) : (term629 _104757 P Q) = (term628 _104757 P Q).
Proof. exact (@lem4369725 _104757 P Q). Qed.
Lemma lem4369727 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1216 _104757 _104758 f s) = (term1217 _104757 _104758 f s).
Proof. exact (@lem4369726 _104757 (term1153 _104757 _104758 f s) (term1173 _104757 _104758 f s)). Qed.
Lemma lem4369728 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1218 _104757 _104758 f s p1) = (term1152 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1218 _104757 _104758 f s p1)). Qed.
Lemma lem4369729 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1219 _104757 _104758 f s) = (term1153 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369728 _104757 _104758 f s p1)). Qed.
Lemma lem4369730 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369731 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1220 _104757 _104758 f s) = (term1154 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369730 _104757) (@lem4369729 _104757 _104758 f s)). Qed.
Lemma lem4369732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369733 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1221 _104757 _104758 f s) = (term1210 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369732) (@lem4369731 _104757 _104758 f s)). Qed.
Lemma lem4369734 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1222 _104757 _104758 f s p1) = (term1172 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1222 _104757 _104758 f s p1)). Qed.
Lemma lem4369735 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1223 _104757 _104758 f s) = (term1173 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369734 _104757 _104758 f s p1)). Qed.
Lemma lem4369736 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369737 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1224 _104757 _104758 f s) = (term1174 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369736 _104757) (@lem4369735 _104757 _104758 f s)). Qed.
Lemma lem4369738 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1216 _104757 _104758 f s) = (term1212 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369733 _104757 _104758 f s) (@lem4369737 _104757 _104758 f s)). Qed.
Lemma lem4369739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369740 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1225 _104757 _104758 f s) = (term1226 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369739) (@lem4369738 _104757 _104758 f s)). Qed.
Lemma lem4369741 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1218 _104757 _104758 f s p1) = (term1152 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1218 _104757 _104758 f s p1)). Qed.
Lemma lem4369742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369743 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1227 _104757 _104758 f s p1) = (term1228 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369742) (@lem4369741 _104757 _104758 f s p1)). Qed.
Lemma lem4369744 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1222 _104757 _104758 f s p1) = (term1172 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1222 _104757 _104758 f s p1)). Qed.
Lemma lem4369745 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1229 _104757 _104758 f s p1) = (term1230 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369743 _104757 _104758 f s p1) (@lem4369744 _104757 _104758 f s p1)). Qed.
Lemma lem4369746 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1231 _104757 _104758 f s) = (term1232 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369745 _104757 _104758 f s p1)). Qed.
Lemma lem4369747 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369748 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1217 _104757 _104758 f s) = (term1233 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369747 _104757) (@lem4369746 _104757 _104758 f s)). Qed.
Lemma lem4369749 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term1216 _104757 _104758 f s) = (term1217 _104757 _104758 f s)) = ((term1212 _104757 _104758 f s) = (term1233 _104757 _104758 f s)).
Proof. exact (MK_COMB (@lem4369740 _104757 _104758 f s) (@lem4369748 _104757 _104758 f s)). Qed.
Lemma lem4369750 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1212 _104757 _104758 f s) = (term1233 _104757 _104758 f s).
Proof. exact (EQ_MP (@lem4369749 _104757 _104758 f s) (@lem4369727 _104757 _104758 f s)). Qed.
Lemma lem4369752 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369753 {_104758 : Type'} (P : _104758 -> Prop) (Q : _104758 -> Prop) : (term629 _104758 P Q) = (term628 _104758 P Q).
Proof. exact (@lem4369752 _104758 P Q). Qed.
Lemma lem4369754 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1234 _104757 _104758 f s p1) = (term1235 _104757 _104758 f s p1).
Proof. exact (@lem4369753 _104758 (term1151 _104757 _104758 f s p1) (term1171 _104757 _104758 f s p1)). Qed.
Lemma lem4369755 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1236 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1236 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369756 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1237 _104757 _104758 f s p1) = (term1151 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369755 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369757 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369758 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1238 _104757 _104758 f s p1) = (term1152 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369757 _104758) (@lem4369756 _104757 _104758 f s p1)). Qed.
Lemma lem4369759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369760 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1239 _104757 _104758 f s p1) = (term1228 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369759) (@lem4369758 _104757 _104758 f s p1)). Qed.
Lemma lem4369761 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1240 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1240 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369762 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1241 _104757 _104758 f s p1) = (term1171 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369761 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369763 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369764 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1242 _104757 _104758 f s p1) = (term1172 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369763 _104758) (@lem4369762 _104757 _104758 f s p1)). Qed.
Lemma lem4369765 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1234 _104757 _104758 f s p1) = (term1230 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369760 _104757 _104758 f s p1) (@lem4369764 _104757 _104758 f s p1)). Qed.
Lemma lem4369766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369767 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1243 _104757 _104758 f s p1) = (term1244 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369766) (@lem4369765 _104757 _104758 f s p1)). Qed.
Lemma lem4369768 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1236 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1236 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369770 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1245 _104757 _104758 f s p1 p2) = (term1246 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369769) (@lem4369768 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369771 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1240 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1240 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369772 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1247 _104757 _104758 f s p1 p2) = (term1248 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369770 _104757 _104758 f s p1 p2) (@lem4369771 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369773 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1249 _104757 _104758 f s p1) = (term1250 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369772 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369774 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369775 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1235 _104757 _104758 f s p1) = (term1251 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369774 _104758) (@lem4369773 _104757 _104758 f s p1)). Qed.
Lemma lem4369776 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : ((term1234 _104757 _104758 f s p1) = (term1235 _104757 _104758 f s p1)) = ((term1230 _104757 _104758 f s p1) = (term1251 _104757 _104758 f s p1)).
Proof. exact (MK_COMB (@lem4369767 _104757 _104758 f s p1) (@lem4369775 _104757 _104758 f s p1)). Qed.
Lemma lem4369777 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1230 _104757 _104758 f s p1) = (term1251 _104757 _104758 f s p1).
Proof. exact (EQ_MP (@lem4369776 _104757 _104758 f s p1) (@lem4369754 _104757 _104758 f s p1)). Qed.
Lemma lem4369779 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369780 {_104758 : Type'} (P : type686 _104758) (Q : type686 _104758) : (term786 _104758 P Q) = (term785 _104758 P Q).
Proof. exact (@lem4369779 (_104758 -> Prop) P Q). Qed.
Lemma lem4369781 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1252 _104757 _104758 f s p1 p2) = (term1253 _104757 _104758 f s p1 p2).
Proof. exact (@lem4369780 _104758 (term1149 _104757 _104758 f s p1 p2) (term1169 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369782 {_104757 _104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1254 _104757 _104758 f s p1 p2 t) = (term1147 _104757 _104758 t f s p1 p2).
Proof. exact (eq_refl (term1254 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369783 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1255 _104757 _104758 f s p1 p2) = (term1149 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369782 _104757 _104758 t f s p1 p2)). Qed.
Lemma lem4369784 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369785 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1256 _104757 _104758 f s p1 p2) = (term1150 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369784 _104758) (@lem4369783 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369787 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1257 _104757 _104758 f s p1 p2) = (term1246 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369786) (@lem4369785 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369788 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1258 _104757 _104758 f s p1 p2 t) = (term1167 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1258 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369789 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1259 _104757 _104758 f s p1 p2) = (term1169 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369788 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369790 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369791 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1260 _104757 _104758 f s p1 p2) = (term1170 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369790 _104758) (@lem4369789 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369792 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1252 _104757 _104758 f s p1 p2) = (term1248 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369787 _104757 _104758 f s p1 p2) (@lem4369791 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369794 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1261 _104757 _104758 f s p1 p2) = (term1262 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369793) (@lem4369792 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369795 {_104757 _104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1254 _104757 _104758 f s p1 p2 t) = (term1147 _104757 _104758 t f s p1 p2).
Proof. exact (eq_refl (term1254 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369797 {_104757 _104758 : Type'} (t : _104758 -> Prop) (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1263 _104757 _104758 f s p1 p2 t) = (term1264 _104757 _104758 t f s p1 p2).
Proof. exact (MK_COMB (@lem4369796) (@lem4369795 _104757 _104758 t f s p1 p2)). Qed.
Lemma lem4369798 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1258 _104757 _104758 f s p1 p2 t) = (term1167 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1258 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4369799 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1265 _104757 _104758 f s p1 p2 t) = (term1266 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4369797 _104757 _104758 t f s p1 p2) (@lem4369798 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369800 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1267 _104757 _104758 f s p1 p2) = (term1268 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4369799 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4369801 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4369802 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1253 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4369801 _104758) (@lem4369800 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369803 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term1252 _104757 _104758 f s p1 p2) = (term1253 _104757 _104758 f s p1 p2)) = ((term1248 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2)).
Proof. exact (MK_COMB (@lem4369794 _104757 _104758 f s p1 p2) (@lem4369802 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369804 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1248 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2).
Proof. exact (EQ_MP (@lem4369803 _104757 _104758 f s p1 p2) (@lem4369781 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369805 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1250 _104757 _104758 f s p1) = (term1270 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4369804 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4369806 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4369807 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1251 _104757 _104758 f s p1) = (term1271 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4369806 _104758) (@lem4369805 _104757 _104758 f s p1)). Qed.
Lemma lem4369808 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1230 _104757 _104758 f s p1) = (term1271 _104757 _104758 f s p1).
Proof. exact (TRANS (@lem4369777 _104757 _104758 f s p1) (@lem4369807 _104757 _104758 f s p1)). Qed.
Lemma lem4369809 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1232 _104757 _104758 f s) = (term1272 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4369808 _104757 _104758 f s p1)). Qed.
Lemma lem4369810 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4369811 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1233 _104757 _104758 f s) = (term1273 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4369810 _104757) (@lem4369809 _104757 _104758 f s)). Qed.
Lemma lem4369812 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1212 _104757 _104758 f s) = (term1273 _104757 _104758 f s).
Proof. exact (TRANS (@lem4369750 _104757 _104758 f s) (@lem4369811 _104757 _104758 f s)). Qed.
Lemma lem4369813 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1214 _104757 _104758 s) = (term1274 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4369812 _104757 _104758 f s)). Qed.
Lemma lem4369814 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4369815 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1215 _104757 _104758 s) = (term1275 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4369814 _104758) (@lem4369813 _104757 _104758 s)). Qed.
Lemma lem4369816 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1194 _104757 _104758 s) = (term1275 _104757 _104758 s).
Proof. exact (TRANS (@lem4369723 _104757 _104758 s) (@lem4369815 _104757 _104758 s)). Qed.
Lemma lem4369817 {_104757 _104758 : Type'} : (term1196 _104757 _104758) = (term1276 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4369816 _104757 _104758 s)). Qed.
Lemma lem4369818 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4369819 {_104757 _104758 : Type'} : (term1197 _104757 _104758) = (term1277 _104757 _104758).
Proof. exact (MK_COMB (@lem4369818 _104757) (@lem4369817 _104757 _104758)). Qed.
Lemma lem4369820 {_104757 _104758 : Type'} : (term1179 _104757 _104758) = (term1277 _104757 _104758).
Proof. exact (TRANS (@lem4369696 _104757 _104758) (@lem4369819 _104757 _104758)). Qed.
Lemma lem4369821 {_104757 _104758 : Type'} : (term806 _104757 _104758) = (term1277 _104757 _104758).
Proof. exact (TRANS (@lem4369669 _104757 _104758) (@lem4369820 _104757 _104758)). Qed.
Lemma lem4369822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369823 {_104757 _104758 : Type'} : (term807 _104757 _104758) = (term1278 _104757 _104758).
Proof. exact (MK_COMB (@lem4369822) (@lem4369821 _104757 _104758)). Qed.
Lemma lem4369825 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369826 {_104795 : Type'} (P : type686 _104795) (Q : Prop) : (term898 _104795 P Q) = (term899 _104795 P Q).
Proof. exact (@lem4369825 (_104795 -> Prop) P Q). Qed.
Lemma lem4369827 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1279 _104795 _104796 f p1 t p2) = (term1280 _104795 _104796 f p1 t p2).
Proof. exact (@lem4369826 _104795 (term363 _104795 f p1) (t p2)). Qed.
Lemma lem4369828 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term431 _104795 f p1 t) = (term361 _104795 f t p1).
Proof. exact (eq_refl (term431 _104795 f p1 t)). Qed.
Lemma lem4369829 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term902 _104795 f p1) = (term363 _104795 f p1).
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4369828 _104795 f t p1)). Qed.
Lemma lem4369830 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369831 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term903 _104795 f p1) = (term364 _104795 f p1).
Proof. exact (MK_COMB (@lem4369830 _104795) (@lem4369829 _104795 f p1)). Qed.
Lemma lem4369832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369833 {_104795 : Type'} (f : type686 _104795) (p1 : _104795) : (term904 _104795 f p1) = (term366 _104795 f p1).
Proof. exact (MK_COMB (@lem4369832) (@lem4369831 _104795 f p1)). Qed.
Lemma lem4369834 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4369835 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1279 _104795 _104796 f p1 t p2) = (term402 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369833 _104795 f p1) (@lem4369834 _104796 t p2)). Qed.
Lemma lem4369836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369837 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1281 _104795 _104796 f p1 t p2) = (term403 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369836) (@lem4369835 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369838 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term431 _104795 f p1 t) = (term361 _104795 f t p1).
Proof. exact (eq_refl (term431 _104795 f p1 t)). Qed.
Lemma lem4369839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369840 {_104795 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) : (term906 _104795 f p1 t) = (term907 _104795 f t p1).
Proof. exact (MK_COMB (@lem4369839) (@lem4369838 _104795 f t p1)). Qed.
Lemma lem4369841 {_104796 : Type'} (t : _104796 -> Prop) (p2 : _104796) : (t p2) = (t p2).
Proof. exact (eq_refl (t p2)). Qed.
Lemma lem4369842 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1282 _104795 _104796 f p1 t t' p2) = (term1283 _104795 _104796 f t p1 t' p2).
Proof. exact (MK_COMB (@lem4369840 _104795 f t p1) (@lem4369841 _104796 t' p2)). Qed.
Lemma lem4369843 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1284 _104795 _104796 f p1 t p2) = (term1285 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4369842 _104795 _104796 f t' p1 t p2)). Qed.
Lemma lem4369844 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369845 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1280 _104795 _104796 f p1 t p2) = (term1286 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369844 _104795) (@lem4369843 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369846 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1279 _104795 _104796 f p1 t p2) = (term1280 _104795 _104796 f p1 t p2)) = ((term402 _104795 _104796 f p1 t p2) = (term1286 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4369837 _104795 _104796 f p1 t p2) (@lem4369845 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369847 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term402 _104795 _104796 f p1 t p2) = (term1286 _104795 _104796 f p1 t p2).
Proof. exact (EQ_MP (@lem4369846 _104795 _104796 f p1 t p2) (@lem4369827 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369849 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term583 _104795 _104796 f p1 t p2) = (term1287 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369848) (@lem4369847 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369850 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term578 _104795 _104796 f p1 t p2) = (term578 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term578 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369851 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term585 _104795 _104796 f p1 t p2) = (term1288 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369849 _104795 _104796 f p1 t p2) (@lem4369850 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369853 {A : Type'} (P : A -> Prop) (Q : Prop) : (term896 A P Q) = (term897 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4369854 {_104795 : Type'} (P : type686 _104795) (Q : Prop) : (term898 _104795 P Q) = (term899 _104795 P Q).
Proof. exact (@lem4369853 (_104795 -> Prop) P Q). Qed.
Lemma lem4369855 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1289 _104795 _104796 f p1 t p2) = (term1290 _104795 _104796 f p1 t p2).
Proof. exact (@lem4369854 _104795 (term1285 _104795 _104796 f p1 t p2) (term578 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369856 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1291 _104795 _104796 f p1 t' p2 t) = (term1283 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1291 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4369857 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1292 _104795 _104796 f p1 t p2) = (term1285 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4369856 _104795 _104796 f t' p1 t p2)). Qed.
Lemma lem4369858 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369859 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1293 _104795 _104796 f p1 t p2) = (term1286 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369858 _104795) (@lem4369857 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369861 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1294 _104795 _104796 f p1 t p2) = (term1287 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369860) (@lem4369859 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369862 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term578 _104795 _104796 f p1 t p2) = (term578 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term578 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369863 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1289 _104795 _104796 f p1 t p2) = (term1288 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369861 _104795 _104796 f p1 t p2) (@lem4369862 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369865 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1295 _104795 _104796 f p1 t p2) = (term1296 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369864) (@lem4369863 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369866 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1291 _104795 _104796 f p1 t' p2 t) = (term1283 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1291 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4369867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4369868 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1297 _104795 _104796 f p1 t' p2 t) = (term1298 _104795 _104796 f t p1 t' p2).
Proof. exact (MK_COMB (@lem4369867) (@lem4369866 _104795 _104796 f t p1 t' p2)). Qed.
Lemma lem4369869 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term578 _104795 _104796 f p1 t p2) = (term578 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term578 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369870 {_104795 _104796 : Type'} (t : _104795 -> Prop) (f : type686 _104795) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1299 _104795 _104796 t f p1 t' p2) = (term1300 _104795 _104796 t f p1 t' p2).
Proof. exact (MK_COMB (@lem4369868 _104795 _104796 f t p1 t' p2) (@lem4369869 _104795 _104796 f p1 t' p2)). Qed.
Lemma lem4369871 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1301 _104795 _104796 f p1 t p2) = (term1302 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4369870 _104795 _104796 t' f p1 t p2)). Qed.
Lemma lem4369872 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369873 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1290 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369872 _104795) (@lem4369871 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369874 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1289 _104795 _104796 f p1 t p2) = (term1290 _104795 _104796 f p1 t p2)) = ((term1288 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4369865 _104795 _104796 f p1 t p2) (@lem4369873 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369875 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1288 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (EQ_MP (@lem4369874 _104795 _104796 f p1 t p2) (@lem4369855 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369876 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term585 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (TRANS (@lem4369851 _104795 _104796 f p1 t p2) (@lem4369875 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369877 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term810 _104795 _104796 f p1 t) = (term1304 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4369876 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369878 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4369879 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term821 _104795 _104796 f p1 t) = (term1305 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4369878 _104796) (@lem4369877 _104795 _104796 f p1 t)). Qed.
Lemma lem4369880 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term832 _104795 _104796 f t) = (term1306 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4369879 _104795 _104796 f p1 t)). Qed.
Lemma lem4369881 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4369882 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term843 _104795 _104796 f t) = (term1307 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369881 _104795) (@lem4369880 _104795 _104796 f t)). Qed.
Lemma lem4369883 {_104795 _104796 : Type'} (f : type686 _104795) : (term854 _104795 _104796 f) = (term1308 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4369882 _104795 _104796 f t)). Qed.
Lemma lem4369884 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4369885 {_104795 _104796 : Type'} (f : type686 _104795) : (term865 _104795 _104796 f) = (term1309 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369884 _104796) (@lem4369883 _104795 _104796 f)). Qed.
Lemma lem4369886 {_104795 _104796 : Type'} : (term876 _104795 _104796) = (term1310 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4369885 _104795 _104796 f)). Qed.
Lemma lem4369887 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4369888 {_104795 _104796 : Type'} : (term887 _104795 _104796) = (term1311 _104795 _104796).
Proof. exact (MK_COMB (@lem4369887 _104795) (@lem4369886 _104795 _104796)). Qed.
Lemma lem4369889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369890 {_104795 _104796 : Type'} : (term889 _104795 _104796) = (term1312 _104795 _104796).
Proof. exact (MK_COMB (@lem4369889) (@lem4369888 _104795 _104796)). Qed.
Lemma lem4369892 {A : Type'} (P : Prop) (Q : A -> Prop) : (term913 A P Q) = (term914 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4369893 {_104795 : Type'} (P : Prop) (Q : type686 _104795) : (term915 _104795 P Q) = (term916 _104795 P Q).
Proof. exact (@lem4369892 (_104795 -> Prop) P Q). Qed.
Lemma lem4369894 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1313 _104795 _104796 f p1 t p2) = (term1314 _104795 _104796 f p1 t p2).
Proof. exact (@lem4369893 _104795 (term567 _104795 _104796 f p1 t p2) (term405 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369895 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term574 _104795 _104796 f p1 t p2 s) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term574 _104795 _104796 f p1 t p2 s)). Qed.
Lemma lem4369896 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1315 _104795 _104796 f p1 t p2) = (term405 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4369895 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4369897 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369898 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1316 _104795 _104796 f p1 t p2) = (term406 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369897 _104795) (@lem4369896 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369899 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term580 _104795 _104796 f p1 t p2) = (term580 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term580 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369900 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1313 _104795 _104796 f p1 t p2) = (term582 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369899 _104795 _104796 f p1 t p2) (@lem4369898 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369902 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1317 _104795 _104796 f p1 t p2) = (term1318 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369901) (@lem4369900 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369903 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term574 _104795 _104796 f p1 t p2 s) = (term404 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term574 _104795 _104796 f p1 t p2 s)). Qed.
Lemma lem4369904 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term580 _104795 _104796 f p1 t p2) = (term580 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term580 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369905 {_104795 _104796 : Type'} (f : type686 _104795) (s : _104795 -> Prop) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1319 _104795 _104796 f p1 t p2 s) = (term1320 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4369904 _104795 _104796 f p1 t p2) (@lem4369903 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4369906 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1321 _104795 _104796 f p1 t p2) = (term1322 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4369905 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4369907 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4369908 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1314 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4369907 _104795) (@lem4369906 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369909 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1313 _104795 _104796 f p1 t p2) = (term1314 _104795 _104796 f p1 t p2)) = ((term582 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4369902 _104795 _104796 f p1 t p2) (@lem4369908 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369910 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term582 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2).
Proof. exact (EQ_MP (@lem4369909 _104795 _104796 f p1 t p2) (@lem4369894 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369911 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term811 _104795 _104796 f p1 t) = (term1324 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4369910 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4369912 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4369913 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term826 _104795 _104796 f p1 t) = (term1325 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4369912 _104796) (@lem4369911 _104795 _104796 f p1 t)). Qed.
Lemma lem4369914 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term833 _104795 _104796 f t) = (term1326 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4369913 _104795 _104796 f p1 t)). Qed.
Lemma lem4369915 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4369916 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term848 _104795 _104796 f t) = (term1327 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369915 _104795) (@lem4369914 _104795 _104796 f t)). Qed.
Lemma lem4369917 {_104795 _104796 : Type'} (f : type686 _104795) : (term855 _104795 _104796 f) = (term1328 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4369916 _104795 _104796 f t)). Qed.
Lemma lem4369918 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4369919 {_104795 _104796 : Type'} (f : type686 _104795) : (term870 _104795 _104796 f) = (term1329 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369918 _104796) (@lem4369917 _104795 _104796 f)). Qed.
Lemma lem4369920 {_104795 _104796 : Type'} : (term877 _104795 _104796) = (term1330 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4369919 _104795 _104796 f)). Qed.
Lemma lem4369921 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4369922 {_104795 _104796 : Type'} : (term892 _104795 _104796) = (term1331 _104795 _104796).
Proof. exact (MK_COMB (@lem4369921 _104795) (@lem4369920 _104795 _104796)). Qed.
Lemma lem4369923 {_104795 _104796 : Type'} : (term893 _104795 _104796) = (term1332 _104795 _104796).
Proof. exact (MK_COMB (@lem4369890 _104795 _104796) (@lem4369922 _104795 _104796)). Qed.
Lemma lem4369925 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369926 {_104795 : Type'} (P : type180 _104795) (Q : type180 _104795) : (term675 _104795 P Q) = (term674 _104795 P Q).
Proof. exact (@lem4369925 (type686 _104795) P Q). Qed.
Lemma lem4369927 {_104795 _104796 : Type'} : (term1333 _104795 _104796) = (term1334 _104795 _104796).
Proof. exact (@lem4369926 _104795 (term1310 _104795 _104796) (term1330 _104795 _104796)). Qed.
Lemma lem4369928 {_104795 _104796 : Type'} (f : type686 _104795) : (term1335 _104795 _104796 f) = (term1309 _104795 _104796 f).
Proof. exact (eq_refl (term1335 _104795 _104796 f)). Qed.
Lemma lem4369929 {_104795 _104796 : Type'} : (term1336 _104795 _104796) = (term1310 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4369928 _104795 _104796 f)). Qed.
Lemma lem4369930 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4369931 {_104795 _104796 : Type'} : (term1337 _104795 _104796) = (term1311 _104795 _104796).
Proof. exact (MK_COMB (@lem4369930 _104795) (@lem4369929 _104795 _104796)). Qed.
Lemma lem4369932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369933 {_104795 _104796 : Type'} : (term1338 _104795 _104796) = (term1312 _104795 _104796).
Proof. exact (MK_COMB (@lem4369932) (@lem4369931 _104795 _104796)). Qed.
Lemma lem4369934 {_104795 _104796 : Type'} (f : type686 _104795) : (term1339 _104795 _104796 f) = (term1329 _104795 _104796 f).
Proof. exact (eq_refl (term1339 _104795 _104796 f)). Qed.
Lemma lem4369935 {_104795 _104796 : Type'} : (term1340 _104795 _104796) = (term1330 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4369934 _104795 _104796 f)). Qed.
Lemma lem4369936 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4369937 {_104795 _104796 : Type'} : (term1341 _104795 _104796) = (term1331 _104795 _104796).
Proof. exact (MK_COMB (@lem4369936 _104795) (@lem4369935 _104795 _104796)). Qed.
Lemma lem4369938 {_104795 _104796 : Type'} : (term1333 _104795 _104796) = (term1332 _104795 _104796).
Proof. exact (MK_COMB (@lem4369933 _104795 _104796) (@lem4369937 _104795 _104796)). Qed.
Lemma lem4369939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369940 {_104795 _104796 : Type'} : (term1342 _104795 _104796) = (term1343 _104795 _104796).
Proof. exact (MK_COMB (@lem4369939) (@lem4369938 _104795 _104796)). Qed.
Lemma lem4369941 {_104795 _104796 : Type'} (f : type686 _104795) : (term1335 _104795 _104796 f) = (term1309 _104795 _104796 f).
Proof. exact (eq_refl (term1335 _104795 _104796 f)). Qed.
Lemma lem4369942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369943 {_104795 _104796 : Type'} (f : type686 _104795) : (term1344 _104795 _104796 f) = (term1345 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369942) (@lem4369941 _104795 _104796 f)). Qed.
Lemma lem4369944 {_104795 _104796 : Type'} (f : type686 _104795) : (term1339 _104795 _104796 f) = (term1329 _104795 _104796 f).
Proof. exact (eq_refl (term1339 _104795 _104796 f)). Qed.
Lemma lem4369945 {_104795 _104796 : Type'} (f : type686 _104795) : (term1346 _104795 _104796 f) = (term1347 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369943 _104795 _104796 f) (@lem4369944 _104795 _104796 f)). Qed.
Lemma lem4369946 {_104795 _104796 : Type'} : (term1348 _104795 _104796) = (term1349 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4369945 _104795 _104796 f)). Qed.
Lemma lem4369947 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4369948 {_104795 _104796 : Type'} : (term1334 _104795 _104796) = (term1350 _104795 _104796).
Proof. exact (MK_COMB (@lem4369947 _104795) (@lem4369946 _104795 _104796)). Qed.
Lemma lem4369949 {_104795 _104796 : Type'} : ((term1333 _104795 _104796) = (term1334 _104795 _104796)) = ((term1332 _104795 _104796) = (term1350 _104795 _104796)).
Proof. exact (MK_COMB (@lem4369940 _104795 _104796) (@lem4369948 _104795 _104796)). Qed.
Lemma lem4369950 {_104795 _104796 : Type'} : (term1332 _104795 _104796) = (term1350 _104795 _104796).
Proof. exact (EQ_MP (@lem4369949 _104795 _104796) (@lem4369927 _104795 _104796)). Qed.
Lemma lem4369952 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369953 {_104796 : Type'} (P : type686 _104796) (Q : type686 _104796) : (term786 _104796 P Q) = (term785 _104796 P Q).
Proof. exact (@lem4369952 (_104796 -> Prop) P Q). Qed.
Lemma lem4369954 {_104795 _104796 : Type'} (f : type686 _104795) : (term1351 _104795 _104796 f) = (term1352 _104795 _104796 f).
Proof. exact (@lem4369953 _104796 (term1308 _104795 _104796 f) (term1328 _104795 _104796 f)). Qed.
Lemma lem4369955 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1353 _104795 _104796 f t) = (term1307 _104795 _104796 f t).
Proof. exact (eq_refl (term1353 _104795 _104796 f t)). Qed.
Lemma lem4369956 {_104795 _104796 : Type'} (f : type686 _104795) : (term1354 _104795 _104796 f) = (term1308 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4369955 _104795 _104796 f t)). Qed.
Lemma lem4369957 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4369958 {_104795 _104796 : Type'} (f : type686 _104795) : (term1355 _104795 _104796 f) = (term1309 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369957 _104796) (@lem4369956 _104795 _104796 f)). Qed.
Lemma lem4369959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369960 {_104795 _104796 : Type'} (f : type686 _104795) : (term1356 _104795 _104796 f) = (term1345 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369959) (@lem4369958 _104795 _104796 f)). Qed.
Lemma lem4369961 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1357 _104795 _104796 f t) = (term1327 _104795 _104796 f t).
Proof. exact (eq_refl (term1357 _104795 _104796 f t)). Qed.
Lemma lem4369962 {_104795 _104796 : Type'} (f : type686 _104795) : (term1358 _104795 _104796 f) = (term1328 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4369961 _104795 _104796 f t)). Qed.
Lemma lem4369963 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4369964 {_104795 _104796 : Type'} (f : type686 _104795) : (term1359 _104795 _104796 f) = (term1329 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369963 _104796) (@lem4369962 _104795 _104796 f)). Qed.
Lemma lem4369965 {_104795 _104796 : Type'} (f : type686 _104795) : (term1351 _104795 _104796 f) = (term1347 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369960 _104795 _104796 f) (@lem4369964 _104795 _104796 f)). Qed.
Lemma lem4369966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369967 {_104795 _104796 : Type'} (f : type686 _104795) : (term1360 _104795 _104796 f) = (term1361 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369966) (@lem4369965 _104795 _104796 f)). Qed.
Lemma lem4369968 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1353 _104795 _104796 f t) = (term1307 _104795 _104796 f t).
Proof. exact (eq_refl (term1353 _104795 _104796 f t)). Qed.
Lemma lem4369969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369970 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1362 _104795 _104796 f t) = (term1363 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369969) (@lem4369968 _104795 _104796 f t)). Qed.
Lemma lem4369971 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1357 _104795 _104796 f t) = (term1327 _104795 _104796 f t).
Proof. exact (eq_refl (term1357 _104795 _104796 f t)). Qed.
Lemma lem4369972 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1364 _104795 _104796 f t) = (term1365 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369970 _104795 _104796 f t) (@lem4369971 _104795 _104796 f t)). Qed.
Lemma lem4369973 {_104795 _104796 : Type'} (f : type686 _104795) : (term1366 _104795 _104796 f) = (term1367 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4369972 _104795 _104796 f t)). Qed.
Lemma lem4369974 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4369975 {_104795 _104796 : Type'} (f : type686 _104795) : (term1352 _104795 _104796 f) = (term1368 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4369974 _104796) (@lem4369973 _104795 _104796 f)). Qed.
Lemma lem4369976 {_104795 _104796 : Type'} (f : type686 _104795) : ((term1351 _104795 _104796 f) = (term1352 _104795 _104796 f)) = ((term1347 _104795 _104796 f) = (term1368 _104795 _104796 f)).
Proof. exact (MK_COMB (@lem4369967 _104795 _104796 f) (@lem4369975 _104795 _104796 f)). Qed.
Lemma lem4369977 {_104795 _104796 : Type'} (f : type686 _104795) : (term1347 _104795 _104796 f) = (term1368 _104795 _104796 f).
Proof. exact (EQ_MP (@lem4369976 _104795 _104796 f) (@lem4369954 _104795 _104796 f)). Qed.
Lemma lem4369979 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4369980 {_104795 : Type'} (P : _104795 -> Prop) (Q : _104795 -> Prop) : (term629 _104795 P Q) = (term628 _104795 P Q).
Proof. exact (@lem4369979 _104795 P Q). Qed.
Lemma lem4369981 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1369 _104795 _104796 f t) = (term1370 _104795 _104796 f t).
Proof. exact (@lem4369980 _104795 (term1306 _104795 _104796 f t) (term1326 _104795 _104796 f t)). Qed.
Lemma lem4369982 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1371 _104795 _104796 f t p1) = (term1305 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1371 _104795 _104796 f t p1)). Qed.
Lemma lem4369983 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1372 _104795 _104796 f t) = (term1306 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4369982 _104795 _104796 f p1 t)). Qed.
Lemma lem4369984 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4369985 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1373 _104795 _104796 f t) = (term1307 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369984 _104795) (@lem4369983 _104795 _104796 f t)). Qed.
Lemma lem4369986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369987 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1374 _104795 _104796 f t) = (term1363 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369986) (@lem4369985 _104795 _104796 f t)). Qed.
Lemma lem4369988 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1375 _104795 _104796 f t p1) = (term1325 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1375 _104795 _104796 f t p1)). Qed.
Lemma lem4369989 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1376 _104795 _104796 f t) = (term1326 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4369988 _104795 _104796 f p1 t)). Qed.
Lemma lem4369990 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4369991 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1377 _104795 _104796 f t) = (term1327 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369990 _104795) (@lem4369989 _104795 _104796 f t)). Qed.
Lemma lem4369992 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1369 _104795 _104796 f t) = (term1365 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369987 _104795 _104796 f t) (@lem4369991 _104795 _104796 f t)). Qed.
Lemma lem4369993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4369994 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1378 _104795 _104796 f t) = (term1379 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4369993) (@lem4369992 _104795 _104796 f t)). Qed.
Lemma lem4369995 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1371 _104795 _104796 f t p1) = (term1305 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1371 _104795 _104796 f t p1)). Qed.
Lemma lem4369996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4369997 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1380 _104795 _104796 f t p1) = (term1381 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4369996) (@lem4369995 _104795 _104796 f p1 t)). Qed.
Lemma lem4369998 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1375 _104795 _104796 f t p1) = (term1325 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1375 _104795 _104796 f t p1)). Qed.
Lemma lem4369999 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1382 _104795 _104796 f t p1) = (term1383 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4369997 _104795 _104796 f p1 t) (@lem4369998 _104795 _104796 f p1 t)). Qed.
Lemma lem4370000 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1384 _104795 _104796 f t) = (term1385 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4369999 _104795 _104796 f p1 t)). Qed.
Lemma lem4370001 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370002 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1370 _104795 _104796 f t) = (term1386 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4370001 _104795) (@lem4370000 _104795 _104796 f t)). Qed.
Lemma lem4370003 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : ((term1369 _104795 _104796 f t) = (term1370 _104795 _104796 f t)) = ((term1365 _104795 _104796 f t) = (term1386 _104795 _104796 f t)).
Proof. exact (MK_COMB (@lem4369994 _104795 _104796 f t) (@lem4370002 _104795 _104796 f t)). Qed.
Lemma lem4370004 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1365 _104795 _104796 f t) = (term1386 _104795 _104796 f t).
Proof. exact (EQ_MP (@lem4370003 _104795 _104796 f t) (@lem4369981 _104795 _104796 f t)). Qed.
Lemma lem4370006 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4370007 {_104796 : Type'} (P : _104796 -> Prop) (Q : _104796 -> Prop) : (term629 _104796 P Q) = (term628 _104796 P Q).
Proof. exact (@lem4370006 _104796 P Q). Qed.
Lemma lem4370008 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1387 _104795 _104796 f p1 t) = (term1388 _104795 _104796 f p1 t).
Proof. exact (@lem4370007 _104796 (term1304 _104795 _104796 f p1 t) (term1324 _104795 _104796 f p1 t)). Qed.
Lemma lem4370009 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1389 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1389 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370010 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1390 _104795 _104796 f p1 t) = (term1304 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4370009 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370011 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370012 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1391 _104795 _104796 f p1 t) = (term1305 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370011 _104796) (@lem4370010 _104795 _104796 f p1 t)). Qed.
Lemma lem4370013 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370014 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1392 _104795 _104796 f p1 t) = (term1381 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370013) (@lem4370012 _104795 _104796 f p1 t)). Qed.
Lemma lem4370015 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1393 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1393 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370016 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1394 _104795 _104796 f p1 t) = (term1324 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4370015 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370017 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370018 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1395 _104795 _104796 f p1 t) = (term1325 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370017 _104796) (@lem4370016 _104795 _104796 f p1 t)). Qed.
Lemma lem4370019 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1387 _104795 _104796 f p1 t) = (term1383 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370014 _104795 _104796 f p1 t) (@lem4370018 _104795 _104796 f p1 t)). Qed.
Lemma lem4370020 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370021 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1396 _104795 _104796 f p1 t) = (term1397 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370020) (@lem4370019 _104795 _104796 f p1 t)). Qed.
Lemma lem4370022 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1389 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1389 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370023 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370024 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1398 _104795 _104796 f p1 t p2) = (term1399 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370023) (@lem4370022 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370025 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1393 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1393 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370026 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1400 _104795 _104796 f p1 t p2) = (term1401 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370024 _104795 _104796 f p1 t p2) (@lem4370025 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370027 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1402 _104795 _104796 f p1 t) = (term1403 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4370026 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370028 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370029 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1388 _104795 _104796 f p1 t) = (term1404 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370028 _104796) (@lem4370027 _104795 _104796 f p1 t)). Qed.
Lemma lem4370030 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : ((term1387 _104795 _104796 f p1 t) = (term1388 _104795 _104796 f p1 t)) = ((term1383 _104795 _104796 f p1 t) = (term1404 _104795 _104796 f p1 t)).
Proof. exact (MK_COMB (@lem4370021 _104795 _104796 f p1 t) (@lem4370029 _104795 _104796 f p1 t)). Qed.
Lemma lem4370031 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1383 _104795 _104796 f p1 t) = (term1404 _104795 _104796 f p1 t).
Proof. exact (EQ_MP (@lem4370030 _104795 _104796 f p1 t) (@lem4370008 _104795 _104796 f p1 t)). Qed.
Lemma lem4370033 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term629 A P Q) = (term628 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4370034 {_104795 : Type'} (P : type686 _104795) (Q : type686 _104795) : (term786 _104795 P Q) = (term785 _104795 P Q).
Proof. exact (@lem4370033 (_104795 -> Prop) P Q). Qed.
Lemma lem4370035 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1405 _104795 _104796 f p1 t p2) = (term1406 _104795 _104796 f p1 t p2).
Proof. exact (@lem4370034 _104795 (term1302 _104795 _104796 f p1 t p2) (term1322 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370036 {_104795 _104796 : Type'} (t : _104795 -> Prop) (f : type686 _104795) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1407 _104795 _104796 f p1 t' p2 t) = (term1300 _104795 _104796 t f p1 t' p2).
Proof. exact (eq_refl (term1407 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370037 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1408 _104795 _104796 f p1 t p2) = (term1302 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4370036 _104795 _104796 t' f p1 t p2)). Qed.
Lemma lem4370038 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370039 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1409 _104795 _104796 f p1 t p2) = (term1303 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370038 _104795) (@lem4370037 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370041 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1410 _104795 _104796 f p1 t p2) = (term1399 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370040) (@lem4370039 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370042 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1411 _104795 _104796 f p1 t' p2 t) = (term1320 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1411 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370043 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1412 _104795 _104796 f p1 t p2) = (term1322 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4370042 _104795 _104796 f t' p1 t p2)). Qed.
Lemma lem4370044 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370045 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1413 _104795 _104796 f p1 t p2) = (term1323 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370044 _104795) (@lem4370043 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370046 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1405 _104795 _104796 f p1 t p2) = (term1401 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370041 _104795 _104796 f p1 t p2) (@lem4370045 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370048 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1414 _104795 _104796 f p1 t p2) = (term1415 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370047) (@lem4370046 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370049 {_104795 _104796 : Type'} (t : _104795 -> Prop) (f : type686 _104795) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1407 _104795 _104796 f p1 t' p2 t) = (term1300 _104795 _104796 t f p1 t' p2).
Proof. exact (eq_refl (term1407 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370051 {_104795 _104796 : Type'} (t : _104795 -> Prop) (f : type686 _104795) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1416 _104795 _104796 f p1 t' p2 t) = (term1417 _104795 _104796 t f p1 t' p2).
Proof. exact (MK_COMB (@lem4370050) (@lem4370049 _104795 _104796 t f p1 t' p2)). Qed.
Lemma lem4370052 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1411 _104795 _104796 f p1 t' p2 t) = (term1320 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1411 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370053 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1418 _104795 _104796 f p1 t' p2 t) = (term1419 _104795 _104796 f t p1 t' p2).
Proof. exact (MK_COMB (@lem4370051 _104795 _104796 t f p1 t' p2) (@lem4370052 _104795 _104796 f t p1 t' p2)). Qed.
Lemma lem4370054 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1420 _104795 _104796 f p1 t p2) = (term1421 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4370053 _104795 _104796 f t' p1 t p2)). Qed.
Lemma lem4370055 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370056 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1406 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370055 _104795) (@lem4370054 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370057 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1405 _104795 _104796 f p1 t p2) = (term1406 _104795 _104796 f p1 t p2)) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)).
Proof. exact (MK_COMB (@lem4370048 _104795 _104796 f p1 t p2) (@lem4370056 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370058 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (EQ_MP (@lem4370057 _104795 _104796 f p1 t p2) (@lem4370035 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370061 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1423 _104795 _104796 f p1 t p2) = (term1423 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1423 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370062 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1423 _104795 _104796 f p1 t p2) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)).
Proof. exact (eq_refl (term1423 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370063 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1424 _104795 _104796 f p1 t p2) = (term1424 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1424 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370064 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1423 _104795 _104796 f p1 t p2) = (term1423 _104795 _104796 f p1 t p2)) = ((term1423 _104795 _104796 f p1 t p2) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2))).
Proof. exact (MK_COMB (@lem4370063 _104795 _104796 f p1 t p2) (@lem4370062 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370065 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1423 _104795 _104796 f p1 t p2) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)).
Proof. exact (eq_refl (term1423 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370067 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1424 _104795 _104796 f p1 t p2) = (term1425 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370066) (@lem4370065 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370068 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)).
Proof. exact (eq_refl ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2))). Qed.
Lemma lem4370069 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1423 _104795 _104796 f p1 t p2) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2))) = (((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2))).
Proof. exact (MK_COMB (@lem4370067 _104795 _104796 f p1 t p2) (@lem4370068 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370070 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1423 _104795 _104796 f p1 t p2) = (term1423 _104795 _104796 f p1 t p2)) = (((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2))).
Proof. exact (TRANS (@lem4370064 _104795 _104796 f p1 t p2) (@lem4370069 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370071 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)) = ((term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2)).
Proof. exact (EQ_MP (@lem4370070 _104795 _104796 f p1 t p2) (@lem4370061 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370072 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1401 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (EQ_MP (@lem4370071 _104795 _104796 f p1 t p2) (@lem4370058 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370073 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1403 _104795 _104796 f p1 t) = (term1426 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4370072 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370074 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370075 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1404 _104795 _104796 f p1 t) = (term1427 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370074 _104796) (@lem4370073 _104795 _104796 f p1 t)). Qed.
Lemma lem4370076 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1383 _104795 _104796 f p1 t) = (term1427 _104795 _104796 f p1 t).
Proof. exact (TRANS (@lem4370031 _104795 _104796 f p1 t) (@lem4370075 _104795 _104796 f p1 t)). Qed.
Lemma lem4370077 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1385 _104795 _104796 f t) = (term1428 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4370076 _104795 _104796 f p1 t)). Qed.
Lemma lem4370078 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370079 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1386 _104795 _104796 f t) = (term1429 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4370078 _104795) (@lem4370077 _104795 _104796 f t)). Qed.
Lemma lem4370080 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1365 _104795 _104796 f t) = (term1429 _104795 _104796 f t).
Proof. exact (TRANS (@lem4370004 _104795 _104796 f t) (@lem4370079 _104795 _104796 f t)). Qed.
Lemma lem4370081 {_104795 _104796 : Type'} (f : type686 _104795) : (term1367 _104795 _104796 f) = (term1430 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4370080 _104795 _104796 f t)). Qed.
Lemma lem4370082 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370083 {_104795 _104796 : Type'} (f : type686 _104795) : (term1368 _104795 _104796 f) = (term1431 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370082 _104796) (@lem4370081 _104795 _104796 f)). Qed.
Lemma lem4370084 {_104795 _104796 : Type'} (f : type686 _104795) : (term1347 _104795 _104796 f) = (term1431 _104795 _104796 f).
Proof. exact (TRANS (@lem4369977 _104795 _104796 f) (@lem4370083 _104795 _104796 f)). Qed.
Lemma lem4370085 {_104795 _104796 : Type'} : (term1349 _104795 _104796) = (term1432 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4370084 _104795 _104796 f)). Qed.
Lemma lem4370086 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370087 {_104795 _104796 : Type'} : (term1350 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (MK_COMB (@lem4370086 _104795) (@lem4370085 _104795 _104796)). Qed.
Lemma lem4370088 {_104795 _104796 : Type'} : (term1332 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (TRANS (@lem4369950 _104795 _104796) (@lem4370087 _104795 _104796)). Qed.
Lemma lem4370089 {_104795 _104796 : Type'} : (term893 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (TRANS (@lem4369923 _104795 _104796) (@lem4370088 _104795 _104796)). Qed.
Lemma lem4370090 {_104757 _104758 _104795 _104796 : Type'} : (term894 _104757 _104758 _104795 _104796) = (term1434 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4369823 _104757 _104758) (@lem4370089 _104795 _104796)). Qed.
Lemma lem4370094 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370095 {_104757 : Type'} (P : type686 _104757) (Q : Prop) : (term1437 _104757 P Q) = (term1438 _104757 P Q).
Proof. exact (@lem4370094 (_104757 -> Prop) P Q). Qed.
Lemma lem4370096 {_104757 _104758 _104795 _104796 : Type'} : (term1439 _104757 _104758 _104795 _104796) = (term1440 _104757 _104758 _104795 _104796).
Proof. exact (@lem4370095 _104757 (term1276 _104757 _104758) (term1433 _104795 _104796)). Qed.
Lemma lem4370097 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1441 _104757 _104758 s) = (term1275 _104757 _104758 s).
Proof. exact (eq_refl (term1441 _104757 _104758 s)). Qed.
Lemma lem4370098 {_104757 _104758 : Type'} : (term1442 _104757 _104758) = (term1276 _104757 _104758).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370097 _104757 _104758 s)). Qed.
Lemma lem4370099 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370100 {_104757 _104758 : Type'} : (term1443 _104757 _104758) = (term1277 _104757 _104758).
Proof. exact (MK_COMB (@lem4370099 _104757) (@lem4370098 _104757 _104758)). Qed.
Lemma lem4370101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370102 {_104757 _104758 : Type'} : (term1444 _104757 _104758) = (term1278 _104757 _104758).
Proof. exact (MK_COMB (@lem4370101) (@lem4370100 _104757 _104758)). Qed.
Lemma lem4370103 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370104 {_104757 _104758 _104795 _104796 : Type'} : (term1439 _104757 _104758 _104795 _104796) = (term1434 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370102 _104757 _104758) (@lem4370103 _104795 _104796)). Qed.
Lemma lem4370105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370106 {_104757 _104758 _104795 _104796 : Type'} : (term1445 _104757 _104758 _104795 _104796) = (term1446 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370105) (@lem4370104 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370107 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1441 _104757 _104758 s) = (term1275 _104757 _104758 s).
Proof. exact (eq_refl (term1441 _104757 _104758 s)). Qed.
Lemma lem4370108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370109 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1447 _104757 _104758 s) = (term1448 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4370108) (@lem4370107 _104757 _104758 s)). Qed.
Lemma lem4370110 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370111 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1449 _104757 _104758 _104795 _104796 s) = (term1450 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370109 _104757 _104758 s) (@lem4370110 _104795 _104796)). Qed.
Lemma lem4370112 {_104757 _104758 _104795 _104796 : Type'} : (term1451 _104757 _104758 _104795 _104796) = (term1452 _104757 _104758 _104795 _104796).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370111 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370113 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370114 {_104757 _104758 _104795 _104796 : Type'} : (term1440 _104757 _104758 _104795 _104796) = (term1453 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370113 _104757) (@lem4370112 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370115 {_104757 _104758 _104795 _104796 : Type'} : ((term1439 _104757 _104758 _104795 _104796) = (term1440 _104757 _104758 _104795 _104796)) = ((term1434 _104757 _104758 _104795 _104796) = (term1453 _104757 _104758 _104795 _104796)).
Proof. exact (MK_COMB (@lem4370106 _104757 _104758 _104795 _104796) (@lem4370114 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370116 {_104757 _104758 _104795 _104796 : Type'} : (term1434 _104757 _104758 _104795 _104796) = (term1453 _104757 _104758 _104795 _104796).
Proof. exact (EQ_MP (@lem4370115 _104757 _104758 _104795 _104796) (@lem4370096 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370120 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370121 {_104758 : Type'} (P : type180 _104758) (Q : Prop) : (term1454 _104758 P Q) = (term1455 _104758 P Q).
Proof. exact (@lem4370120 (type686 _104758) P Q). Qed.
Lemma lem4370122 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1456 _104757 _104758 _104795 _104796 s) = (term1457 _104757 _104758 _104795 _104796 s).
Proof. exact (@lem4370121 _104758 (term1274 _104757 _104758 s) (term1433 _104795 _104796)). Qed.
Lemma lem4370123 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1458 _104757 _104758 s f) = (term1273 _104757 _104758 f s).
Proof. exact (eq_refl (term1458 _104757 _104758 s f)). Qed.
Lemma lem4370124 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1459 _104757 _104758 s) = (term1274 _104757 _104758 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4370123 _104757 _104758 f s)). Qed.
Lemma lem4370125 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370126 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1460 _104757 _104758 s) = (term1275 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4370125 _104758) (@lem4370124 _104757 _104758 s)). Qed.
Lemma lem4370127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370128 {_104757 _104758 : Type'} (s : _104757 -> Prop) : (term1461 _104757 _104758 s) = (term1448 _104757 _104758 s).
Proof. exact (MK_COMB (@lem4370127) (@lem4370126 _104757 _104758 s)). Qed.
Lemma lem4370129 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370130 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1456 _104757 _104758 _104795 _104796 s) = (term1450 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370128 _104757 _104758 s) (@lem4370129 _104795 _104796)). Qed.
Lemma lem4370131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370132 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1462 _104757 _104758 _104795 _104796 s) = (term1463 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370131) (@lem4370130 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370133 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1458 _104757 _104758 s f) = (term1273 _104757 _104758 f s).
Proof. exact (eq_refl (term1458 _104757 _104758 s f)). Qed.
Lemma lem4370134 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370135 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1464 _104757 _104758 s f) = (term1465 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4370134) (@lem4370133 _104757 _104758 f s)). Qed.
Lemma lem4370136 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370137 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1466 _104757 _104758 _104795 _104796 s f) = (term1467 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370135 _104757 _104758 f s) (@lem4370136 _104795 _104796)). Qed.
Lemma lem4370138 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1468 _104757 _104758 _104795 _104796 s) = (term1469 _104757 _104758 _104795 _104796 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4370137 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370139 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370140 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1457 _104757 _104758 _104795 _104796 s) = (term1470 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370139 _104758) (@lem4370138 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370141 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : ((term1456 _104757 _104758 _104795 _104796 s) = (term1457 _104757 _104758 _104795 _104796 s)) = ((term1450 _104757 _104758 _104795 _104796 s) = (term1470 _104757 _104758 _104795 _104796 s)).
Proof. exact (MK_COMB (@lem4370132 _104757 _104758 _104795 _104796 s) (@lem4370140 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370142 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1450 _104757 _104758 _104795 _104796 s) = (term1470 _104757 _104758 _104795 _104796 s).
Proof. exact (EQ_MP (@lem4370141 _104757 _104758 _104795 _104796 s) (@lem4370122 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370146 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370147 {_104757 : Type'} (P : _104757 -> Prop) (Q : Prop) : (term1435 _104757 P Q) = (term1436 _104757 P Q).
Proof. exact (@lem4370146 _104757 P Q). Qed.
Lemma lem4370148 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1471 _104757 _104758 _104795 _104796 f s) = (term1472 _104757 _104758 _104795 _104796 f s).
Proof. exact (@lem4370147 _104757 (term1272 _104757 _104758 f s) (term1433 _104795 _104796)). Qed.
Lemma lem4370149 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1473 _104757 _104758 f s p1) = (term1271 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1473 _104757 _104758 f s p1)). Qed.
Lemma lem4370150 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1474 _104757 _104758 f s) = (term1272 _104757 _104758 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4370149 _104757 _104758 f s p1)). Qed.
Lemma lem4370151 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370152 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1475 _104757 _104758 f s) = (term1273 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4370151 _104757) (@lem4370150 _104757 _104758 f s)). Qed.
Lemma lem4370153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370154 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1476 _104757 _104758 f s) = (term1465 _104757 _104758 f s).
Proof. exact (MK_COMB (@lem4370153) (@lem4370152 _104757 _104758 f s)). Qed.
Lemma lem4370155 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370156 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1471 _104757 _104758 _104795 _104796 f s) = (term1467 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370154 _104757 _104758 f s) (@lem4370155 _104795 _104796)). Qed.
Lemma lem4370157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370158 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1477 _104757 _104758 _104795 _104796 f s) = (term1478 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370157) (@lem4370156 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370159 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1473 _104757 _104758 f s p1) = (term1271 _104757 _104758 f s p1).
Proof. exact (eq_refl (term1473 _104757 _104758 f s p1)). Qed.
Lemma lem4370160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370161 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1479 _104757 _104758 f s p1) = (term1480 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4370160) (@lem4370159 _104757 _104758 f s p1)). Qed.
Lemma lem4370162 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370163 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1481 _104757 _104758 _104795 _104796 f s p1) = (term1482 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370161 _104757 _104758 f s p1) (@lem4370162 _104795 _104796)). Qed.
Lemma lem4370164 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1483 _104757 _104758 _104795 _104796 f s) = (term1484 _104757 _104758 _104795 _104796 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4370163 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370165 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370166 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1472 _104757 _104758 _104795 _104796 f s) = (term1485 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370165 _104757) (@lem4370164 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370167 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : ((term1471 _104757 _104758 _104795 _104796 f s) = (term1472 _104757 _104758 _104795 _104796 f s)) = ((term1467 _104757 _104758 _104795 _104796 f s) = (term1485 _104757 _104758 _104795 _104796 f s)).
Proof. exact (MK_COMB (@lem4370158 _104757 _104758 _104795 _104796 f s) (@lem4370166 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370168 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1467 _104757 _104758 _104795 _104796 f s) = (term1485 _104757 _104758 _104795 _104796 f s).
Proof. exact (EQ_MP (@lem4370167 _104757 _104758 _104795 _104796 f s) (@lem4370148 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370172 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370173 {_104758 : Type'} (P : _104758 -> Prop) (Q : Prop) : (term1435 _104758 P Q) = (term1436 _104758 P Q).
Proof. exact (@lem4370172 _104758 P Q). Qed.
Lemma lem4370174 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1486 _104757 _104758 _104795 _104796 f s p1) = (term1487 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (@lem4370173 _104758 (term1270 _104757 _104758 f s p1) (term1433 _104795 _104796)). Qed.
Lemma lem4370175 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1488 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1488 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370176 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1489 _104757 _104758 f s p1) = (term1270 _104757 _104758 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4370175 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370177 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370178 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1490 _104757 _104758 f s p1) = (term1271 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4370177 _104758) (@lem4370176 _104757 _104758 f s p1)). Qed.
Lemma lem4370179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370180 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1491 _104757 _104758 f s p1) = (term1480 _104757 _104758 f s p1).
Proof. exact (MK_COMB (@lem4370179) (@lem4370178 _104757 _104758 f s p1)). Qed.
Lemma lem4370181 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370182 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1486 _104757 _104758 _104795 _104796 f s p1) = (term1482 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370180 _104757 _104758 f s p1) (@lem4370181 _104795 _104796)). Qed.
Lemma lem4370183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370184 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1492 _104757 _104758 _104795 _104796 f s p1) = (term1493 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370183) (@lem4370182 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370185 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1488 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2).
Proof. exact (eq_refl (term1488 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370187 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1494 _104757 _104758 f s p1 p2) = (term1495 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4370186) (@lem4370185 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370188 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370189 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1496 _104757 _104758 _104795 _104796 f s p1 p2) = (term1497 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370187 _104757 _104758 f s p1 p2) (@lem4370188 _104795 _104796)). Qed.
Lemma lem4370190 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1498 _104757 _104758 _104795 _104796 f s p1) = (term1499 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4370189 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370191 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370192 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1487 _104757 _104758 _104795 _104796 f s p1) = (term1500 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370191 _104758) (@lem4370190 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370193 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : ((term1486 _104757 _104758 _104795 _104796 f s p1) = (term1487 _104757 _104758 _104795 _104796 f s p1)) = ((term1482 _104757 _104758 _104795 _104796 f s p1) = (term1500 _104757 _104758 _104795 _104796 f s p1)).
Proof. exact (MK_COMB (@lem4370184 _104757 _104758 _104795 _104796 f s p1) (@lem4370192 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370194 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1482 _104757 _104758 _104795 _104796 f s p1) = (term1500 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (EQ_MP (@lem4370193 _104757 _104758 _104795 _104796 f s p1) (@lem4370174 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370198 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370199 {_104758 : Type'} (P : type686 _104758) (Q : Prop) : (term1437 _104758 P Q) = (term1438 _104758 P Q).
Proof. exact (@lem4370198 (_104758 -> Prop) P Q). Qed.
Lemma lem4370200 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1501 _104757 _104758 _104795 _104796 f s p1 p2) = (term1502 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (@lem4370199 _104758 (term1268 _104757 _104758 f s p1 p2) (term1433 _104795 _104796)). Qed.
Lemma lem4370201 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1503 _104757 _104758 f s p1 p2 t) = (term1266 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1503 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4370202 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1504 _104757 _104758 f s p1 p2) = (term1268 _104757 _104758 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4370201 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370203 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370204 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1505 _104757 _104758 f s p1 p2) = (term1269 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4370203 _104758) (@lem4370202 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370206 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1506 _104757 _104758 f s p1 p2) = (term1495 _104757 _104758 f s p1 p2).
Proof. exact (MK_COMB (@lem4370205) (@lem4370204 _104757 _104758 f s p1 p2)). Qed.
Lemma lem4370207 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370208 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1501 _104757 _104758 _104795 _104796 f s p1 p2) = (term1497 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370206 _104757 _104758 f s p1 p2) (@lem4370207 _104795 _104796)). Qed.
Lemma lem4370209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370210 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1507 _104757 _104758 _104795 _104796 f s p1 p2) = (term1508 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370209) (@lem4370208 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370211 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1503 _104757 _104758 f s p1 p2 t) = (term1266 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1503 _104757 _104758 f s p1 p2 t)). Qed.
Lemma lem4370212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370213 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1509 _104757 _104758 f s p1 p2 t) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370212) (@lem4370211 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370214 {_104795 _104796 : Type'} : (term1433 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (eq_refl (term1433 _104795 _104796)). Qed.
Lemma lem4370215 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1511 _104757 _104758 _104795 _104796 f s p1 p2 t) = (term1512 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370213 _104757 _104758 f s p1 t p2) (@lem4370214 _104795 _104796)). Qed.
Lemma lem4370216 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1513 _104757 _104758 _104795 _104796 f s p1 p2) = (term1514 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4370215 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370217 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370218 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1502 _104757 _104758 _104795 _104796 f s p1 p2) = (term1515 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370217 _104758) (@lem4370216 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370219 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : ((term1501 _104757 _104758 _104795 _104796 f s p1 p2) = (term1502 _104757 _104758 _104795 _104796 f s p1 p2)) = ((term1497 _104757 _104758 _104795 _104796 f s p1 p2) = (term1515 _104757 _104758 _104795 _104796 f s p1 p2)).
Proof. exact (MK_COMB (@lem4370210 _104757 _104758 _104795 _104796 f s p1 p2) (@lem4370218 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370220 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1497 _104757 _104758 _104795 _104796 f s p1 p2) = (term1515 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (EQ_MP (@lem4370219 _104757 _104758 _104795 _104796 f s p1 p2) (@lem4370200 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370223 {_104795 : Type'} (P : Prop) (Q : type180 _104795) : (term1518 _104795 P Q) = (term1519 _104795 P Q).
Proof. exact (@lem4370222 (type686 _104795) P Q). Qed.
Lemma lem4370224 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1520 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1521 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (@lem4370223 _104795 (term1266 _104757 _104758 f s p1 t p2) (term1432 _104795 _104796)). Qed.
Lemma lem4370225 {_104795 _104796 : Type'} (f : type686 _104795) : (term1522 _104795 _104796 f) = (term1431 _104795 _104796 f).
Proof. exact (eq_refl (term1522 _104795 _104796 f)). Qed.
Lemma lem4370226 {_104795 _104796 : Type'} : (term1523 _104795 _104796) = (term1432 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104795 => @lem4370225 _104795 _104796 f)). Qed.
Lemma lem4370227 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370228 {_104795 _104796 : Type'} : (term1524 _104795 _104796) = (term1433 _104795 _104796).
Proof. exact (MK_COMB (@lem4370227 _104795) (@lem4370226 _104795 _104796)). Qed.
Lemma lem4370229 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370230 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1520 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1512 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370229 _104757 _104758 f s p1 t p2) (@lem4370228 _104795 _104796)). Qed.
Lemma lem4370231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370232 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1525 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1526 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370231) (@lem4370230 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370233 {_104795 _104796 : Type'} (f : type686 _104795) : (term1522 _104795 _104796 f) = (term1431 _104795 _104796 f).
Proof. exact (eq_refl (term1522 _104795 _104796 f)). Qed.
Lemma lem4370234 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370235 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1527 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1528 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370234 _104757 _104758 f s p1 t p2) (@lem4370233 _104795 _104796 f')). Qed.
Lemma lem4370236 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1529 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1530 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (fun_ext (fun f' : type686 _104795 => @lem4370235 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370237 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370238 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1521 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1531 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370237 _104795) (@lem4370236 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370239 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : ((term1520 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1521 _104757 _104758 _104795 _104796 f s p1 t p2)) = ((term1512 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1531 _104757 _104758 _104795 _104796 f s p1 t p2)).
Proof. exact (MK_COMB (@lem4370232 _104757 _104758 _104795 _104796 f s p1 t p2) (@lem4370238 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370240 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1512 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1531 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (EQ_MP (@lem4370239 _104757 _104758 _104795 _104796 f s p1 t p2) (@lem4370224 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370242 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370243 {_104796 : Type'} (P : Prop) (Q : type686 _104796) : (term1532 _104796 P Q) = (term1533 _104796 P Q).
Proof. exact (@lem4370242 (_104796 -> Prop) P Q). Qed.
Lemma lem4370244 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1534 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1535 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (@lem4370243 _104796 (term1266 _104757 _104758 f s p1 t p2) (term1430 _104795 _104796 f')). Qed.
Lemma lem4370245 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1536 _104795 _104796 f t) = (term1429 _104795 _104796 f t).
Proof. exact (eq_refl (term1536 _104795 _104796 f t)). Qed.
Lemma lem4370246 {_104795 _104796 : Type'} (f : type686 _104795) : (term1537 _104795 _104796 f) = (term1430 _104795 _104796 f).
Proof. exact (fun_ext (fun t : _104796 -> Prop => @lem4370245 _104795 _104796 f t)). Qed.
Lemma lem4370247 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370248 {_104795 _104796 : Type'} (f : type686 _104795) : (term1538 _104795 _104796 f) = (term1431 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370247 _104796) (@lem4370246 _104795 _104796 f)). Qed.
Lemma lem4370249 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370250 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1534 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1528 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370249 _104757 _104758 f s p1 t p2) (@lem4370248 _104795 _104796 f')). Qed.
Lemma lem4370251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370252 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1539 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1540 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370251) (@lem4370250 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370253 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1536 _104795 _104796 f t) = (term1429 _104795 _104796 f t).
Proof. exact (eq_refl (term1536 _104795 _104796 f t)). Qed.
Lemma lem4370254 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370255 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1541 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1542 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370254 _104757 _104758 f s p1 t p2) (@lem4370253 _104795 _104796 f' t')). Qed.
Lemma lem4370256 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1543 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1544 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (fun_ext (fun t' : _104796 -> Prop => @lem4370255 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370257 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370258 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1535 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1545 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370257 _104796) (@lem4370256 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370259 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : ((term1534 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1535 _104757 _104758 _104795 _104796 f s p1 t p2 f')) = ((term1528 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1545 _104757 _104758 _104795 _104796 f s p1 t p2 f')).
Proof. exact (MK_COMB (@lem4370252 _104757 _104758 _104795 _104796 f s p1 t p2 f') (@lem4370258 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370260 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1528 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1545 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (EQ_MP (@lem4370259 _104757 _104758 _104795 _104796 f s p1 t p2 f') (@lem4370244 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370262 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370263 {_104795 : Type'} (P : Prop) (Q : _104795 -> Prop) : (term1516 _104795 P Q) = (term1517 _104795 P Q).
Proof. exact (@lem4370262 _104795 P Q). Qed.
Lemma lem4370264 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1546 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1547 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (@lem4370263 _104795 (term1266 _104757 _104758 f s p1 t p2) (term1428 _104795 _104796 f' t')). Qed.
Lemma lem4370265 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1548 _104795 _104796 f t p1) = (term1427 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1548 _104795 _104796 f t p1)). Qed.
Lemma lem4370266 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1549 _104795 _104796 f t) = (term1428 _104795 _104796 f t).
Proof. exact (fun_ext (fun p1 : _104795 => @lem4370265 _104795 _104796 f p1 t)). Qed.
Lemma lem4370267 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370268 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104796 -> Prop) : (term1550 _104795 _104796 f t) = (term1429 _104795 _104796 f t).
Proof. exact (MK_COMB (@lem4370267 _104795) (@lem4370266 _104795 _104796 f t)). Qed.
Lemma lem4370269 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370270 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1546 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1542 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370269 _104757 _104758 f s p1 t p2) (@lem4370268 _104795 _104796 f' t')). Qed.
Lemma lem4370271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370272 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1551 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1552 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370271) (@lem4370270 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370273 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1548 _104795 _104796 f t p1) = (term1427 _104795 _104796 f p1 t).
Proof. exact (eq_refl (term1548 _104795 _104796 f t p1)). Qed.
Lemma lem4370274 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370275 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1553 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1') = (term1554 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370274 _104757 _104758 f s p1 t p2) (@lem4370273 _104795 _104796 f' p1' t')). Qed.
Lemma lem4370276 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1555 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1556 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (fun_ext (fun p1' : _104795 => @lem4370275 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370277 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370278 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1547 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1557 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370277 _104795) (@lem4370276 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370279 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : ((term1546 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1547 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')) = ((term1542 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1557 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')).
Proof. exact (MK_COMB (@lem4370272 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') (@lem4370278 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370280 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1542 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1557 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (EQ_MP (@lem4370279 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') (@lem4370264 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370282 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370283 {_104796 : Type'} (P : Prop) (Q : _104796 -> Prop) : (term1516 _104796 P Q) = (term1517 _104796 P Q).
Proof. exact (@lem4370282 _104796 P Q). Qed.
Lemma lem4370284 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1558 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1559 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (@lem4370283 _104796 (term1266 _104757 _104758 f s p1 t p2) (term1426 _104795 _104796 f' p1' t')). Qed.
Lemma lem4370285 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1560 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1560 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370286 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1561 _104795 _104796 f p1 t) = (term1426 _104795 _104796 f p1 t).
Proof. exact (fun_ext (fun p2 : _104796 => @lem4370285 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370287 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370288 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) : (term1562 _104795 _104796 f p1 t) = (term1427 _104795 _104796 f p1 t).
Proof. exact (MK_COMB (@lem4370287 _104796) (@lem4370286 _104795 _104796 f p1 t)). Qed.
Lemma lem4370289 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370290 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1558 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1554 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370289 _104757 _104758 f s p1 t p2) (@lem4370288 _104795 _104796 f' p1' t')). Qed.
Lemma lem4370291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370292 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1563 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1564 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370291) (@lem4370290 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370293 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1560 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (eq_refl (term1560 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370294 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370295 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1565 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1566 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (MK_COMB (@lem4370294 _104757 _104758 f s p1 t p2) (@lem4370293 _104795 _104796 f' p1' t' p2')). Qed.
Lemma lem4370296 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1567 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1568 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (fun_ext (fun p2' : _104796 => @lem4370295 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370297 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370298 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1559 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1569 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370297 _104796) (@lem4370296 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370299 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : ((term1558 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1559 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')) = ((term1554 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1569 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')).
Proof. exact (MK_COMB (@lem4370292 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') (@lem4370298 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370300 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1554 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1569 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (EQ_MP (@lem4370299 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') (@lem4370284 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370302 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370303 {_104795 : Type'} (P : Prop) (Q : type686 _104795) : (term1532 _104795 P Q) = (term1533 _104795 P Q).
Proof. exact (@lem4370302 (_104795 -> Prop) P Q). Qed.
Lemma lem4370304 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1570 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1571 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (@lem4370303 _104795 (term1266 _104757 _104758 f s p1 t p2) (term1421 _104795 _104796 f' p1' t' p2')). Qed.
Lemma lem4370305 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1572 _104795 _104796 f p1 t' p2 t) = (term1419 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1572 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370306 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1573 _104795 _104796 f p1 t p2) = (term1421 _104795 _104796 f p1 t p2).
Proof. exact (fun_ext (fun t' : _104795 -> Prop => @lem4370305 _104795 _104796 f t' p1 t p2)). Qed.
Lemma lem4370307 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370308 {_104795 _104796 : Type'} (f : type686 _104795) (p1 : _104795) (t : _104796 -> Prop) (p2 : _104796) : (term1574 _104795 _104796 f p1 t p2) = (term1422 _104795 _104796 f p1 t p2).
Proof. exact (MK_COMB (@lem4370307 _104795) (@lem4370306 _104795 _104796 f p1 t p2)). Qed.
Lemma lem4370309 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370310 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1570 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1566 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (MK_COMB (@lem4370309 _104757 _104758 f s p1 t p2) (@lem4370308 _104795 _104796 f' p1' t' p2')). Qed.
Lemma lem4370311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370312 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1575 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1576 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (MK_COMB (@lem4370311) (@lem4370310 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370313 {_104795 _104796 : Type'} (f : type686 _104795) (t : _104795 -> Prop) (p1 : _104795) (t' : _104796 -> Prop) (p2 : _104796) : (term1572 _104795 _104796 f p1 t' p2 t) = (term1419 _104795 _104796 f t p1 t' p2).
Proof. exact (eq_refl (term1572 _104795 _104796 f p1 t' p2 t)). Qed.
Lemma lem4370314 {_104757 _104758 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1510 _104757 _104758 f s p1 t p2) = (term1510 _104757 _104758 f s p1 t p2).
Proof. exact (eq_refl (term1510 _104757 _104758 f s p1 t p2)). Qed.
Lemma lem4370315 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104795 -> Prop) (p1' : _104795) (t'' : _104796 -> Prop) (p2' : _104796) : (term1577 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t'' p2' t') = (term1578 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1' t'' p2').
Proof. exact (MK_COMB (@lem4370314 _104757 _104758 f s p1 t p2) (@lem4370313 _104795 _104796 f' t' p1' t'' p2')). Qed.
Lemma lem4370316 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1579 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1580 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (fun_ext (fun t'' : _104795 -> Prop => @lem4370315 _104757 _104758 _104795 _104796 f s p1 t p2 f' t'' p1' t' p2')). Qed.
Lemma lem4370317 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370318 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1571 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (MK_COMB (@lem4370317 _104795) (@lem4370316 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370319 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : ((term1570 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1571 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')) = ((term1566 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')).
Proof. exact (MK_COMB (@lem4370312 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') (@lem4370318 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370320 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1566 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (EQ_MP (@lem4370319 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') (@lem4370304 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370321 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1568 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1582 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (fun_ext (fun p2' : _104796 => @lem4370320 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370322 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370323 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1569 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1583 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370322 _104796) (@lem4370321 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370324 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1554 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1583 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (TRANS (@lem4370300 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') (@lem4370323 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370325 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1556 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1584 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (fun_ext (fun p1' : _104795 => @lem4370324 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370326 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370327 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1557 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1585 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370326 _104795) (@lem4370325 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370328 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1542 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1585 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (TRANS (@lem4370280 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') (@lem4370327 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370329 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1544 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1586 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (fun_ext (fun t' : _104796 -> Prop => @lem4370328 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370330 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370331 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1545 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1587 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370330 _104796) (@lem4370329 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370332 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1528 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1587 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (TRANS (@lem4370260 _104757 _104758 _104795 _104796 f s p1 t p2 f') (@lem4370331 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370333 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1530 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1588 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (fun_ext (fun f' : type686 _104795 => @lem4370332 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370334 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370335 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1531 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1589 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370334 _104795) (@lem4370333 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370336 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1512 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1589 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (TRANS (@lem4370240 _104757 _104758 _104795 _104796 f s p1 t p2) (@lem4370335 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370337 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1514 _104757 _104758 _104795 _104796 f s p1 p2) = (term1590 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4370336 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370338 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370339 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1515 _104757 _104758 _104795 _104796 f s p1 p2) = (term1591 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370338 _104758) (@lem4370337 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370340 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1497 _104757 _104758 _104795 _104796 f s p1 p2) = (term1591 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (TRANS (@lem4370220 _104757 _104758 _104795 _104796 f s p1 p2) (@lem4370339 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370341 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1499 _104757 _104758 _104795 _104796 f s p1) = (term1592 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4370340 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370342 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370343 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1500 _104757 _104758 _104795 _104796 f s p1) = (term1593 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370342 _104758) (@lem4370341 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370344 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1482 _104757 _104758 _104795 _104796 f s p1) = (term1593 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (TRANS (@lem4370194 _104757 _104758 _104795 _104796 f s p1) (@lem4370343 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370345 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1484 _104757 _104758 _104795 _104796 f s) = (term1594 _104757 _104758 _104795 _104796 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4370344 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370346 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370347 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1485 _104757 _104758 _104795 _104796 f s) = (term1595 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370346 _104757) (@lem4370345 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370348 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1467 _104757 _104758 _104795 _104796 f s) = (term1595 _104757 _104758 _104795 _104796 f s).
Proof. exact (TRANS (@lem4370168 _104757 _104758 _104795 _104796 f s) (@lem4370347 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370349 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1469 _104757 _104758 _104795 _104796 s) = (term1596 _104757 _104758 _104795 _104796 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4370348 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370350 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370351 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1470 _104757 _104758 _104795 _104796 s) = (term1597 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370350 _104758) (@lem4370349 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370352 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1450 _104757 _104758 _104795 _104796 s) = (term1597 _104757 _104758 _104795 _104796 s).
Proof. exact (TRANS (@lem4370142 _104757 _104758 _104795 _104796 s) (@lem4370351 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370353 {_104757 _104758 _104795 _104796 : Type'} : (term1452 _104757 _104758 _104795 _104796) = (term1598 _104757 _104758 _104795 _104796).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370352 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370354 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370355 {_104757 _104758 _104795 _104796 : Type'} : (term1453 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370354 _104757) (@lem4370353 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370356 {_104757 _104758 _104795 _104796 : Type'} : (term1434 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4370116 _104757 _104758 _104795 _104796) (@lem4370355 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370357 {_104757 _104758 _104795 _104796 : Type'} : (term894 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4370090 _104757 _104758 _104795 _104796) (@lem4370356 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370358 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term895 _104717 _104718 _104757 _104758 _104795 _104796) = (term1600 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4369573 _104717 _104718) (@lem4370357 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370362 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370363 {_104717 : Type'} (P : type180 _104717) (Q : Prop) : (term1454 _104717 P Q) = (term1455 _104717 P Q).
Proof. exact (@lem4370362 (type686 _104717) P Q). Qed.
Lemma lem4370364 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1601 _104717 _104718 _104757 _104758 _104795 _104796) = (term1602 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (@lem4370363 _104717 (term1123 _104717 _104718) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370365 {_104717 _104718 : Type'} (f : type686 _104717) : (term1603 _104717 _104718 f) = (term1122 _104717 _104718 f).
Proof. exact (eq_refl (term1603 _104717 _104718 f)). Qed.
Lemma lem4370366 {_104717 _104718 : Type'} : (term1604 _104717 _104718) = (term1123 _104717 _104718).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4370365 _104717 _104718 f)). Qed.
Lemma lem4370367 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4370368 {_104717 _104718 : Type'} : (term1605 _104717 _104718) = (term1124 _104717 _104718).
Proof. exact (MK_COMB (@lem4370367 _104717) (@lem4370366 _104717 _104718)). Qed.
Lemma lem4370369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370370 {_104717 _104718 : Type'} : (term1606 _104717 _104718) = (term1125 _104717 _104718).
Proof. exact (MK_COMB (@lem4370369) (@lem4370368 _104717 _104718)). Qed.
Lemma lem4370371 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370372 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1601 _104717 _104718 _104757 _104758 _104795 _104796) = (term1600 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370370 _104717 _104718) (@lem4370371 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370374 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1607 _104717 _104718 _104757 _104758 _104795 _104796) = (term1608 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370373) (@lem4370372 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370375 {_104717 _104718 : Type'} (f : type686 _104717) : (term1603 _104717 _104718 f) = (term1122 _104717 _104718 f).
Proof. exact (eq_refl (term1603 _104717 _104718 f)). Qed.
Lemma lem4370376 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370377 {_104717 _104718 : Type'} (f : type686 _104717) : (term1609 _104717 _104718 f) = (term1610 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4370376) (@lem4370375 _104717 _104718 f)). Qed.
Lemma lem4370378 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370379 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1611 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1612 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370377 _104717 _104718 f) (@lem4370378 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370380 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1613 _104717 _104718 _104757 _104758 _104795 _104796) = (term1614 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4370379 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370381 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4370382 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1602 _104717 _104718 _104757 _104758 _104795 _104796) = (term1615 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370381 _104717) (@lem4370380 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370383 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : ((term1601 _104717 _104718 _104757 _104758 _104795 _104796) = (term1602 _104717 _104718 _104757 _104758 _104795 _104796)) = ((term1600 _104717 _104718 _104757 _104758 _104795 _104796) = (term1615 _104717 _104718 _104757 _104758 _104795 _104796)).
Proof. exact (MK_COMB (@lem4370374 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370382 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370384 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1600 _104717 _104718 _104757 _104758 _104795 _104796) = (term1615 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (EQ_MP (@lem4370383 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370364 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370388 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370389 {_104718 : Type'} (P : type180 _104718) (Q : Prop) : (term1454 _104718 P Q) = (term1455 _104718 P Q).
Proof. exact (@lem4370388 (type686 _104718) P Q). Qed.
Lemma lem4370390 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1616 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1617 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (@lem4370389 _104718 (term1121 _104717 _104718 f) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370391 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1618 _104717 _104718 f g) = (term1120 _104717 _104718 f g).
Proof. exact (eq_refl (term1618 _104717 _104718 f g)). Qed.
Lemma lem4370392 {_104717 _104718 : Type'} (f : type686 _104717) : (term1619 _104717 _104718 f) = (term1121 _104717 _104718 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4370391 _104717 _104718 f g)). Qed.
Lemma lem4370393 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4370394 {_104717 _104718 : Type'} (f : type686 _104717) : (term1620 _104717 _104718 f) = (term1122 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4370393 _104718) (@lem4370392 _104717 _104718 f)). Qed.
Lemma lem4370395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370396 {_104717 _104718 : Type'} (f : type686 _104717) : (term1621 _104717 _104718 f) = (term1610 _104717 _104718 f).
Proof. exact (MK_COMB (@lem4370395) (@lem4370394 _104717 _104718 f)). Qed.
Lemma lem4370397 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370398 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1616 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1612 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370396 _104717 _104718 f) (@lem4370397 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370400 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1622 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1623 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370399) (@lem4370398 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370401 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1618 _104717 _104718 f g) = (term1120 _104717 _104718 f g).
Proof. exact (eq_refl (term1618 _104717 _104718 f g)). Qed.
Lemma lem4370402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370403 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1624 _104717 _104718 f g) = (term1625 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4370402) (@lem4370401 _104717 _104718 f g)). Qed.
Lemma lem4370404 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370405 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1626 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1627 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (MK_COMB (@lem4370403 _104717 _104718 f g) (@lem4370404 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370406 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1628 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1629 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4370405 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370407 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4370408 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1617 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1630 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370407 _104718) (@lem4370406 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370409 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : ((term1616 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1617 _104717 _104718 _104757 _104758 _104795 _104796 f)) = ((term1612 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1630 _104717 _104718 _104757 _104758 _104795 _104796 f)).
Proof. exact (MK_COMB (@lem4370400 _104717 _104718 _104757 _104758 _104795 _104796 f) (@lem4370408 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370410 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1612 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1630 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (EQ_MP (@lem4370409 _104717 _104718 _104757 _104758 _104795 _104796 f) (@lem4370390 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370414 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370415 {_104717 : Type'} (P : _104717 -> Prop) (Q : Prop) : (term1435 _104717 P Q) = (term1436 _104717 P Q).
Proof. exact (@lem4370414 _104717 P Q). Qed.
Lemma lem4370416 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1631 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1632 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (@lem4370415 _104717 (term1119 _104717 _104718 f g) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370417 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1633 _104717 _104718 f g p1) = (term1118 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1633 _104717 _104718 f g p1)). Qed.
Lemma lem4370418 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1634 _104717 _104718 f g) = (term1119 _104717 _104718 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4370417 _104717 _104718 f g p1)). Qed.
Lemma lem4370419 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4370420 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1635 _104717 _104718 f g) = (term1120 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4370419 _104717) (@lem4370418 _104717 _104718 f g)). Qed.
Lemma lem4370421 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370422 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1636 _104717 _104718 f g) = (term1625 _104717 _104718 f g).
Proof. exact (MK_COMB (@lem4370421) (@lem4370420 _104717 _104718 f g)). Qed.
Lemma lem4370423 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370424 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1631 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1627 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (MK_COMB (@lem4370422 _104717 _104718 f g) (@lem4370423 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370426 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1637 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1638 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (MK_COMB (@lem4370425) (@lem4370424 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370427 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1633 _104717 _104718 f g p1) = (term1118 _104717 _104718 f g p1).
Proof. exact (eq_refl (term1633 _104717 _104718 f g p1)). Qed.
Lemma lem4370428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370429 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1639 _104717 _104718 f g p1) = (term1640 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4370428) (@lem4370427 _104717 _104718 f g p1)). Qed.
Lemma lem4370430 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370431 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1641 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1642 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (MK_COMB (@lem4370429 _104717 _104718 f g p1) (@lem4370430 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370432 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1643 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1644 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4370431 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370433 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4370434 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1632 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1645 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (MK_COMB (@lem4370433 _104717) (@lem4370432 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370435 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : ((term1631 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1632 _104717 _104718 _104757 _104758 _104795 _104796 f g)) = ((term1627 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1645 _104717 _104718 _104757 _104758 _104795 _104796 f g)).
Proof. exact (MK_COMB (@lem4370426 _104717 _104718 _104757 _104758 _104795 _104796 f g) (@lem4370434 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370436 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1627 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1645 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (EQ_MP (@lem4370435 _104717 _104718 _104757 _104758 _104795 _104796 f g) (@lem4370416 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370441 {_104718 : Type'} (P : _104718 -> Prop) (Q : Prop) : (term1435 _104718 P Q) = (term1436 _104718 P Q).
Proof. exact (@lem4370440 _104718 P Q). Qed.
Lemma lem4370442 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1646 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1647 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (@lem4370441 _104718 (term1117 _104717 _104718 f g p1) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370443 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1648 _104717 _104718 f g p1 p2) = (term1116 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1648 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370444 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1649 _104717 _104718 f g p1) = (term1117 _104717 _104718 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4370443 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370445 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4370446 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1650 _104717 _104718 f g p1) = (term1118 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4370445 _104718) (@lem4370444 _104717 _104718 f g p1)). Qed.
Lemma lem4370447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370448 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1651 _104717 _104718 f g p1) = (term1640 _104717 _104718 f g p1).
Proof. exact (MK_COMB (@lem4370447) (@lem4370446 _104717 _104718 f g p1)). Qed.
Lemma lem4370449 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370450 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1646 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1642 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (MK_COMB (@lem4370448 _104717 _104718 f g p1) (@lem4370449 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370452 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1652 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1653 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (MK_COMB (@lem4370451) (@lem4370450 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370453 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1648 _104717 _104718 f g p1 p2) = (term1116 _104717 _104718 f g p1 p2).
Proof. exact (eq_refl (term1648 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370454 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370455 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1654 _104717 _104718 f g p1 p2) = (term1655 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4370454) (@lem4370453 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370456 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370457 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1656 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1657 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (MK_COMB (@lem4370455 _104717 _104718 f g p1 p2) (@lem4370456 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370458 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1658 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1659 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4370457 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370459 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4370460 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1647 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1660 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (MK_COMB (@lem4370459 _104718) (@lem4370458 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370461 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : ((term1646 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1647 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)) = ((term1642 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1660 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)).
Proof. exact (MK_COMB (@lem4370452 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) (@lem4370460 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370462 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1642 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1660 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (EQ_MP (@lem4370461 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) (@lem4370442 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370466 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370467 {_104717 : Type'} (P : type686 _104717) (Q : Prop) : (term1437 _104717 P Q) = (term1438 _104717 P Q).
Proof. exact (@lem4370466 (_104717 -> Prop) P Q). Qed.
Lemma lem4370468 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1661 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1662 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (@lem4370467 _104717 (term1115 _104717 _104718 f g p1 p2) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370469 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1663 _104717 _104718 f g p1 p2 t) = (term1114 _104717 _104718 f g t p1 p2).
Proof. exact (eq_refl (term1663 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4370470 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1664 _104717 _104718 f g p1 p2) = (term1115 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4370469 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4370471 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4370472 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1665 _104717 _104718 f g p1 p2) = (term1116 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4370471 _104717) (@lem4370470 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370473 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370474 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1666 _104717 _104718 f g p1 p2) = (term1655 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4370473) (@lem4370472 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4370475 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370476 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1661 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1657 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (MK_COMB (@lem4370474 _104717 _104718 f g p1 p2) (@lem4370475 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370477 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370478 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1667 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1668 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (MK_COMB (@lem4370477) (@lem4370476 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370479 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1663 _104717 _104718 f g p1 p2 t) = (term1114 _104717 _104718 f g t p1 p2).
Proof. exact (eq_refl (term1663 _104717 _104718 f g p1 p2 t)). Qed.
Lemma lem4370480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370481 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1669 _104717 _104718 f g p1 p2 t) = (term1670 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370480) (@lem4370479 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4370482 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370483 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1671 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2 t) = (term1672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370481 _104717 _104718 f g t p1 p2) (@lem4370482 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370484 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1673 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1674 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4370483 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370485 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4370486 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1662 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1675 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (MK_COMB (@lem4370485 _104717) (@lem4370484 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370487 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : ((term1661 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1662 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)) = ((term1657 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1675 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)).
Proof. exact (MK_COMB (@lem4370478 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) (@lem4370486 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370488 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1657 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1675 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (EQ_MP (@lem4370487 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) (@lem4370468 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370492 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1435 A P Q) = (term1436 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4370493 {_104718 : Type'} (P : type686 _104718) (Q : Prop) : (term1437 _104718 P Q) = (term1438 _104718 P Q).
Proof. exact (@lem4370492 (_104718 -> Prop) P Q). Qed.
Lemma lem4370494 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1676 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1677 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (@lem4370493 _104718 (term1113 _104717 _104718 f g t p1 p2) (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370495 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1678 _104717 _104718 f g t p1 p2 t') = (term1111 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1678 _104717 _104718 f g t p1 p2 t')). Qed.
Lemma lem4370496 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1679 _104717 _104718 f g t p1 p2) = (term1113 _104717 _104718 f g t p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4370495 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370497 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4370498 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1680 _104717 _104718 f g t p1 p2) = (term1114 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370497 _104718) (@lem4370496 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4370499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370500 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1681 _104717 _104718 f g t p1 p2) = (term1670 _104717 _104718 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370499) (@lem4370498 _104717 _104718 f g t p1 p2)). Qed.
Lemma lem4370501 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370502 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1676 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370500 _104717 _104718 f g t p1 p2) (@lem4370501 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370503 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370504 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1682 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1683 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370503) (@lem4370502 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370505 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1678 _104717 _104718 f g t p1 p2 t') = (term1111 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1678 _104717 _104718 f g t p1 p2 t')). Qed.
Lemma lem4370506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370507 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1684 _104717 _104718 f g t p1 p2 t') = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370506) (@lem4370505 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370508 {_104757 _104758 _104795 _104796 : Type'} : (term1599 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (eq_refl (term1599 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370509 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1686 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2 t') = (term1687 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370507 _104717 _104718 f g t p1 t' p2) (@lem4370508 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370510 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1688 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1689 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4370509 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370511 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4370512 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1677 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1690 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370511 _104718) (@lem4370510 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370513 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : ((term1676 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1677 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)) = ((term1672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1690 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)).
Proof. exact (MK_COMB (@lem4370504 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) (@lem4370512 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370514 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1690 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (EQ_MP (@lem4370513 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) (@lem4370494 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370516 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370517 {_104757 : Type'} (P : Prop) (Q : type686 _104757) : (term1532 _104757 P Q) = (term1533 _104757 P Q).
Proof. exact (@lem4370516 (_104757 -> Prop) P Q). Qed.
Lemma lem4370518 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1691 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1692 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (@lem4370517 _104757 (term1111 _104717 _104718 f g t p1 t' p2) (term1598 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370519 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1693 _104757 _104758 _104795 _104796 s) = (term1597 _104757 _104758 _104795 _104796 s).
Proof. exact (eq_refl (term1693 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370520 {_104757 _104758 _104795 _104796 : Type'} : (term1694 _104757 _104758 _104795 _104796) = (term1598 _104757 _104758 _104795 _104796).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370519 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370521 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370522 {_104757 _104758 _104795 _104796 : Type'} : (term1695 _104757 _104758 _104795 _104796) = (term1599 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370521 _104757) (@lem4370520 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370523 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370524 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1691 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1687 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370523 _104717 _104718 f g t p1 t' p2) (@lem4370522 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370525 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370526 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1696 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1697 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370525) (@lem4370524 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370527 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1693 _104757 _104758 _104795 _104796 s) = (term1597 _104757 _104758 _104795 _104796 s).
Proof. exact (eq_refl (term1693 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370528 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370529 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1698 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1699 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (MK_COMB (@lem4370528 _104717 _104718 f g t p1 t' p2) (@lem4370527 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370530 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1700 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1701 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370529 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370531 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370532 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1692 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1702 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370531 _104757) (@lem4370530 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370533 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : ((term1691 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1692 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)) = ((term1687 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1702 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)).
Proof. exact (MK_COMB (@lem4370526 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) (@lem4370532 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370534 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1687 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1702 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (EQ_MP (@lem4370533 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) (@lem4370518 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370536 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370537 {_104758 : Type'} (P : Prop) (Q : type180 _104758) : (term1518 _104758 P Q) = (term1519 _104758 P Q).
Proof. exact (@lem4370536 (type686 _104758) P Q). Qed.
Lemma lem4370538 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1703 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1704 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (@lem4370537 _104758 (term1111 _104717 _104718 f g t p1 t' p2) (term1596 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370539 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1705 _104757 _104758 _104795 _104796 s f) = (term1595 _104757 _104758 _104795 _104796 f s).
Proof. exact (eq_refl (term1705 _104757 _104758 _104795 _104796 s f)). Qed.
Lemma lem4370540 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1706 _104757 _104758 _104795 _104796 s) = (term1596 _104757 _104758 _104795 _104796 s).
Proof. exact (fun_ext (fun f : type686 _104758 => @lem4370539 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370541 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370542 {_104757 _104758 _104795 _104796 : Type'} (s : _104757 -> Prop) : (term1707 _104757 _104758 _104795 _104796 s) = (term1597 _104757 _104758 _104795 _104796 s).
Proof. exact (MK_COMB (@lem4370541 _104758) (@lem4370540 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370543 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370544 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1703 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1699 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (MK_COMB (@lem4370543 _104717 _104718 f g t p1 t' p2) (@lem4370542 _104757 _104758 _104795 _104796 s)). Qed.
Lemma lem4370545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370546 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1708 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1709 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (MK_COMB (@lem4370545) (@lem4370544 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370547 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1705 _104757 _104758 _104795 _104796 s f) = (term1595 _104757 _104758 _104795 _104796 f s).
Proof. exact (eq_refl (term1705 _104757 _104758 _104795 _104796 s f)). Qed.
Lemma lem4370548 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370549 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1710 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s f') = (term1711 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (MK_COMB (@lem4370548 _104717 _104718 f g t p1 t' p2) (@lem4370547 _104757 _104758 _104795 _104796 f' s)). Qed.
Lemma lem4370550 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1712 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1713 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (fun_ext (fun f' : type686 _104758 => @lem4370549 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370551 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370552 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1704 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1714 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (MK_COMB (@lem4370551 _104758) (@lem4370550 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370553 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : ((term1703 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1704 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)) = ((term1699 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1714 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)).
Proof. exact (MK_COMB (@lem4370546 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) (@lem4370552 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370554 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1699 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1714 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (EQ_MP (@lem4370553 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) (@lem4370538 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370556 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370557 {_104757 : Type'} (P : Prop) (Q : _104757 -> Prop) : (term1516 _104757 P Q) = (term1517 _104757 P Q).
Proof. exact (@lem4370556 _104757 P Q). Qed.
Lemma lem4370558 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1715 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1716 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (@lem4370557 _104757 (term1111 _104717 _104718 f g t p1 t' p2) (term1594 _104757 _104758 _104795 _104796 f' s)). Qed.
Lemma lem4370559 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1717 _104757 _104758 _104795 _104796 f s p1) = (term1593 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (eq_refl (term1717 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370560 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1718 _104757 _104758 _104795 _104796 f s) = (term1594 _104757 _104758 _104795 _104796 f s).
Proof. exact (fun_ext (fun p1 : _104757 => @lem4370559 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370561 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370562 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) : (term1719 _104757 _104758 _104795 _104796 f s) = (term1595 _104757 _104758 _104795 _104796 f s).
Proof. exact (MK_COMB (@lem4370561 _104757) (@lem4370560 _104757 _104758 _104795 _104796 f s)). Qed.
Lemma lem4370563 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370564 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1715 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1711 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (MK_COMB (@lem4370563 _104717 _104718 f g t p1 t' p2) (@lem4370562 _104757 _104758 _104795 _104796 f' s)). Qed.
Lemma lem4370565 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370566 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1720 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1721 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (MK_COMB (@lem4370565) (@lem4370564 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370567 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1717 _104757 _104758 _104795 _104796 f s p1) = (term1593 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (eq_refl (term1717 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370568 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370569 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1722 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (MK_COMB (@lem4370568 _104717 _104718 f g t p1 t' p2) (@lem4370567 _104757 _104758 _104795 _104796 f' s p1')). Qed.
Lemma lem4370570 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1724 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1725 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (fun_ext (fun p1' : _104757 => @lem4370569 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370571 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370572 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1716 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1726 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (MK_COMB (@lem4370571 _104757) (@lem4370570 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370573 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : ((term1715 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1716 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)) = ((term1711 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1726 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)).
Proof. exact (MK_COMB (@lem4370566 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) (@lem4370572 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370574 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1711 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1726 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (EQ_MP (@lem4370573 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) (@lem4370558 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370576 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370577 {_104758 : Type'} (P : Prop) (Q : _104758 -> Prop) : (term1516 _104758 P Q) = (term1517 _104758 P Q).
Proof. exact (@lem4370576 _104758 P Q). Qed.
Lemma lem4370578 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1727 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1728 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (@lem4370577 _104758 (term1111 _104717 _104718 f g t p1 t' p2) (term1592 _104757 _104758 _104795 _104796 f' s p1')). Qed.
Lemma lem4370579 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1729 _104757 _104758 _104795 _104796 f s p1 p2) = (term1591 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (eq_refl (term1729 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370580 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1730 _104757 _104758 _104795 _104796 f s p1) = (term1592 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (fun_ext (fun p2 : _104758 => @lem4370579 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370581 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370582 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) : (term1731 _104757 _104758 _104795 _104796 f s p1) = (term1593 _104757 _104758 _104795 _104796 f s p1).
Proof. exact (MK_COMB (@lem4370581 _104758) (@lem4370580 _104757 _104758 _104795 _104796 f s p1)). Qed.
Lemma lem4370583 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370584 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1727 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (MK_COMB (@lem4370583 _104717 _104718 f g t p1 t' p2) (@lem4370582 _104757 _104758 _104795 _104796 f' s p1')). Qed.
Lemma lem4370585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370586 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1732 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1733 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (MK_COMB (@lem4370585) (@lem4370584 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370587 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1729 _104757 _104758 _104795 _104796 f s p1 p2) = (term1591 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (eq_refl (term1729 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370588 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370589 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1734 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (MK_COMB (@lem4370588 _104717 _104718 f g t p1 t' p2) (@lem4370587 _104757 _104758 _104795 _104796 f' s p1' p2')). Qed.
Lemma lem4370590 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1736 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1737 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (fun_ext (fun p2' : _104758 => @lem4370589 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370591 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370592 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1728 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1738 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (MK_COMB (@lem4370591 _104758) (@lem4370590 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370593 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : ((term1727 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1728 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')) = ((term1723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1738 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')).
Proof. exact (MK_COMB (@lem4370586 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') (@lem4370592 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370594 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1738 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (EQ_MP (@lem4370593 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') (@lem4370578 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370596 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370597 {_104758 : Type'} (P : Prop) (Q : type686 _104758) : (term1532 _104758 P Q) = (term1533 _104758 P Q).
Proof. exact (@lem4370596 (_104758 -> Prop) P Q). Qed.
Lemma lem4370598 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1739 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1740 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (@lem4370597 _104758 (term1111 _104717 _104718 f g t p1 t' p2) (term1590 _104757 _104758 _104795 _104796 f' s p1' p2')). Qed.
Lemma lem4370599 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1741 _104757 _104758 _104795 _104796 f s p1 p2 t) = (term1589 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term1741 _104757 _104758 _104795 _104796 f s p1 p2 t)). Qed.
Lemma lem4370600 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1742 _104757 _104758 _104795 _104796 f s p1 p2) = (term1590 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4370599 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370601 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370602 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (p2 : _104758) : (term1743 _104757 _104758 _104795 _104796 f s p1 p2) = (term1591 _104757 _104758 _104795 _104796 f s p1 p2).
Proof. exact (MK_COMB (@lem4370601 _104758) (@lem4370600 _104757 _104758 _104795 _104796 f s p1 p2)). Qed.
Lemma lem4370603 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370604 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1739 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (MK_COMB (@lem4370603 _104717 _104718 f g t p1 t' p2) (@lem4370602 _104757 _104758 _104795 _104796 f' s p1' p2')). Qed.
Lemma lem4370605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370606 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1744 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1745 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (MK_COMB (@lem4370605) (@lem4370604 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370607 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1741 _104757 _104758 _104795 _104796 f s p1 p2 t) = (term1589 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (eq_refl (term1741 _104757 _104758 _104795 _104796 f s p1 p2 t)). Qed.
Lemma lem4370608 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370609 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1746 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2' t'') = (term1747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370608 _104717 _104718 f g t p1 t' p2) (@lem4370607 _104757 _104758 _104795 _104796 f' s p1' t'' p2')). Qed.
Lemma lem4370610 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1748 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1749 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (fun_ext (fun t'' : _104758 -> Prop => @lem4370609 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370611 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370612 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1740 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1750 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (MK_COMB (@lem4370611 _104758) (@lem4370610 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370613 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : ((term1739 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1740 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')) = ((term1735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1750 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')).
Proof. exact (MK_COMB (@lem4370606 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') (@lem4370612 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370614 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1750 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (EQ_MP (@lem4370613 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') (@lem4370598 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370616 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370617 {_104795 : Type'} (P : Prop) (Q : type180 _104795) : (term1518 _104795 P Q) = (term1519 _104795 P Q).
Proof. exact (@lem4370616 (type686 _104795) P Q). Qed.
Lemma lem4370618 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1751 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1752 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (@lem4370617 _104795 (term1111 _104717 _104718 f g t p1 t' p2) (term1588 _104757 _104758 _104795 _104796 f' s p1' t'' p2')). Qed.
Lemma lem4370619 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1753 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1587 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (eq_refl (term1753 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370620 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1754 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1588 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (fun_ext (fun f' : type686 _104795 => @lem4370619 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370621 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370622 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) : (term1755 _104757 _104758 _104795 _104796 f s p1 t p2) = (term1589 _104757 _104758 _104795 _104796 f s p1 t p2).
Proof. exact (MK_COMB (@lem4370621 _104795) (@lem4370620 _104757 _104758 _104795 _104796 f s p1 t p2)). Qed.
Lemma lem4370623 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370624 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1751 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370623 _104717 _104718 f g t p1 t' p2) (@lem4370622 _104757 _104758 _104795 _104796 f' s p1' t'' p2')). Qed.
Lemma lem4370625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370626 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1756 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1757 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370625) (@lem4370624 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370627 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1753 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1587 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (eq_refl (term1753 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370628 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370629 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1758 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1759 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (MK_COMB (@lem4370628 _104717 _104718 f g t p1 t' p2) (@lem4370627 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370630 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1760 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1761 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (fun_ext (fun f'' : type686 _104795 => @lem4370629 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370631 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370632 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1752 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1762 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370631 _104795) (@lem4370630 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370633 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : ((term1751 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1752 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')) = ((term1747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1762 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')).
Proof. exact (MK_COMB (@lem4370626 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') (@lem4370632 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370634 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1762 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (EQ_MP (@lem4370633 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') (@lem4370618 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370636 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370637 {_104796 : Type'} (P : Prop) (Q : type686 _104796) : (term1532 _104796 P Q) = (term1533 _104796 P Q).
Proof. exact (@lem4370636 (_104796 -> Prop) P Q). Qed.
Lemma lem4370638 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1763 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1764 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (@lem4370637 _104796 (term1111 _104717 _104718 f g t p1 t' p2) (term1586 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370639 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1765 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1585 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (eq_refl (term1765 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370640 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1766 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1586 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (fun_ext (fun t' : _104796 -> Prop => @lem4370639 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370641 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370642 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) : (term1767 _104757 _104758 _104795 _104796 f s p1 t p2 f') = (term1587 _104757 _104758 _104795 _104796 f s p1 t p2 f').
Proof. exact (MK_COMB (@lem4370641 _104796) (@lem4370640 _104757 _104758 _104795 _104796 f s p1 t p2 f')). Qed.
Lemma lem4370643 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370644 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1763 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1759 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (MK_COMB (@lem4370643 _104717 _104718 f g t p1 t' p2) (@lem4370642 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370646 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1768 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1769 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (MK_COMB (@lem4370645) (@lem4370644 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370647 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1765 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1585 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (eq_refl (term1765 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370648 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370649 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1770 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1771 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (MK_COMB (@lem4370648 _104717 _104718 f g t p1 t' p2) (@lem4370647 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370650 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1772 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1773 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (fun_ext (fun t''' : _104796 -> Prop => @lem4370649 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370651 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370652 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1764 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1774 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (MK_COMB (@lem4370651 _104796) (@lem4370650 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370653 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : ((term1763 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1764 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')) = ((term1759 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1774 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')).
Proof. exact (MK_COMB (@lem4370646 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') (@lem4370652 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370654 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1759 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1774 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (EQ_MP (@lem4370653 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') (@lem4370638 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370656 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370657 {_104795 : Type'} (P : Prop) (Q : _104795 -> Prop) : (term1516 _104795 P Q) = (term1517 _104795 P Q).
Proof. exact (@lem4370656 _104795 P Q). Qed.
Lemma lem4370658 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1775 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1776 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (@lem4370657 _104795 (term1111 _104717 _104718 f g t p1 t' p2) (term1584 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370659 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1777 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1') = (term1583 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (eq_refl (term1777 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1')). Qed.
Lemma lem4370660 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1778 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1584 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (fun_ext (fun p1' : _104795 => @lem4370659 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370661 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370662 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104796 -> Prop) : (term1779 _104757 _104758 _104795 _104796 f s p1 t p2 f' t') = (term1585 _104757 _104758 _104795 _104796 f s p1 t p2 f' t').
Proof. exact (MK_COMB (@lem4370661 _104795) (@lem4370660 _104757 _104758 _104795 _104796 f s p1 t p2 f' t')). Qed.
Lemma lem4370663 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370664 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1775 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1771 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (MK_COMB (@lem4370663 _104717 _104718 f g t p1 t' p2) (@lem4370662 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370666 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1780 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1781 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (MK_COMB (@lem4370665) (@lem4370664 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370667 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1777 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1') = (term1583 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (eq_refl (term1777 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1')). Qed.
Lemma lem4370668 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370669 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1782 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' p1'') = (term1783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (MK_COMB (@lem4370668 _104717 _104718 f g t p1 t' p2) (@lem4370667 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370670 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1784 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1785 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (fun_ext (fun p1'' : _104795 => @lem4370669 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370671 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370672 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1776 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1786 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (MK_COMB (@lem4370671 _104795) (@lem4370670 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370673 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : ((term1775 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1776 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')) = ((term1771 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1786 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')).
Proof. exact (MK_COMB (@lem4370666 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') (@lem4370672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370674 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1771 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1786 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (EQ_MP (@lem4370673 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') (@lem4370658 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370676 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370677 {_104796 : Type'} (P : Prop) (Q : _104796 -> Prop) : (term1516 _104796 P Q) = (term1517 _104796 P Q).
Proof. exact (@lem4370676 _104796 P Q). Qed.
Lemma lem4370678 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1787 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1788 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (@lem4370677 _104796 (term1111 _104717 _104718 f g t p1 t' p2) (term1582 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370679 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1789 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (eq_refl (term1789 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370680 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1790 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1582 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (fun_ext (fun p2' : _104796 => @lem4370679 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370681 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370682 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) : (term1791 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t') = (term1583 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t').
Proof. exact (MK_COMB (@lem4370681 _104796) (@lem4370680 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t')). Qed.
Lemma lem4370683 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370684 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1787 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (MK_COMB (@lem4370683 _104717 _104718 f g t p1 t' p2) (@lem4370682 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370686 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1792 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1793 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (MK_COMB (@lem4370685) (@lem4370684 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370687 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1789 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (eq_refl (term1789 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370688 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370689 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1794 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1795 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370688 _104717 _104718 f g t p1 t' p2) (@lem4370687 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370690 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1796 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1797 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (fun_ext (fun p2'' : _104796 => @lem4370689 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370691 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370692 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1788 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1798 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (MK_COMB (@lem4370691 _104796) (@lem4370690 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370693 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : ((term1787 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1788 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')) = ((term1783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1798 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')).
Proof. exact (MK_COMB (@lem4370686 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') (@lem4370692 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370694 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1798 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (EQ_MP (@lem4370693 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') (@lem4370678 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370696 {A : Type'} (P : Prop) (Q : A -> Prop) : (term1516 A P Q) = (term1517 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4370697 {_104795 : Type'} (P : Prop) (Q : type686 _104795) : (term1532 _104795 P Q) = (term1533 _104795 P Q).
Proof. exact (@lem4370696 (_104795 -> Prop) P Q). Qed.
Lemma lem4370698 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1799 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1800 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (@lem4370697 _104795 (term1111 _104717 _104718 f g t p1 t' p2) (term1580 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370699 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104795 -> Prop) (p1' : _104795) (t'' : _104796 -> Prop) (p2' : _104796) : (term1801 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t'' p2' t') = (term1578 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1' t'' p2').
Proof. exact (eq_refl (term1801 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t'' p2' t')). Qed.
Lemma lem4370700 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1802 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1580 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (fun_ext (fun t'' : _104795 -> Prop => @lem4370699 _104757 _104758 _104795 _104796 f s p1 t p2 f' t'' p1' t' p2')). Qed.
Lemma lem4370701 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370702 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (p1' : _104795) (t' : _104796 -> Prop) (p2' : _104796) : (term1803 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2') = (term1581 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2').
Proof. exact (MK_COMB (@lem4370701 _104795) (@lem4370700 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t' p2')). Qed.
Lemma lem4370703 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370704 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1799 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1795 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370703 _104717 _104718 f g t p1 t' p2) (@lem4370702 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4370706 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1804 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1805 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370705) (@lem4370704 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370707 {_104757 _104758 _104795 _104796 : Type'} (f : type686 _104758) (s : _104757 -> Prop) (p1 : _104757) (t : _104758 -> Prop) (p2 : _104758) (f' : type686 _104795) (t' : _104795 -> Prop) (p1' : _104795) (t'' : _104796 -> Prop) (p2' : _104796) : (term1801 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t'' p2' t') = (term1578 _104757 _104758 _104795 _104796 f s p1 t p2 f' t' p1' t'' p2').
Proof. exact (eq_refl (term1801 _104757 _104758 _104795 _104796 f s p1 t p2 f' p1' t'' p2' t')). Qed.
Lemma lem4370708 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1685 _104717 _104718 f g t p1 t' p2).
Proof. exact (eq_refl (term1685 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4370709 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104795 -> Prop) (p1'' : _104795) (t'''' : _104796 -> Prop) (p2'' : _104796) : (term1806 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t'''' p2'' t''') = (term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' p1'' t'''' p2'').
Proof. exact (MK_COMB (@lem4370708 _104717 _104718 f g t p1 t' p2) (@lem4370707 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t''' p1'' t'''' p2'')). Qed.
Lemma lem4370710 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1808 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1809 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (fun_ext (fun t'''' : _104795 -> Prop => @lem4370709 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4370711 {_104795 : Type'} : (@ex (_104795 -> Prop)) = (@ex (_104795 -> Prop)).
Proof. exact (eq_refl (@ex (_104795 -> Prop))). Qed.
Lemma lem4370712 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1800 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370711 _104795) (@lem4370710 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370713 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : ((term1799 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1800 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')) = ((term1795 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')).
Proof. exact (MK_COMB (@lem4370706 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') (@lem4370712 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370714 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1795 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') = (term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'').
Proof. exact (EQ_MP (@lem4370713 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') (@lem4370698 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370715 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1797 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1811 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (fun_ext (fun p2'' : _104796 => @lem4370714 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'')). Qed.
Lemma lem4370716 {_104796 : Type'} : (@ex _104796) = (@ex _104796).
Proof. exact (eq_refl (@ex _104796)). Qed.
Lemma lem4370717 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1798 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1812 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (MK_COMB (@lem4370716 _104796) (@lem4370715 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370718 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) : (term1783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') = (term1812 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''').
Proof. exact (TRANS (@lem4370694 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') (@lem4370717 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370719 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1785 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1813 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (fun_ext (fun p1'' : _104795 => @lem4370718 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''')). Qed.
Lemma lem4370720 {_104795 : Type'} : (@ex _104795) = (@ex _104795).
Proof. exact (eq_refl (@ex _104795)). Qed.
Lemma lem4370721 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1786 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1814 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (MK_COMB (@lem4370720 _104795) (@lem4370719 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370722 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) : (term1771 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') = (term1814 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''').
Proof. exact (TRANS (@lem4370674 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') (@lem4370721 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370723 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1773 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1815 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (fun_ext (fun t''' : _104796 -> Prop => @lem4370722 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''')). Qed.
Lemma lem4370724 {_104796 : Type'} : (@ex (_104796 -> Prop)) = (@ex (_104796 -> Prop)).
Proof. exact (eq_refl (@ex (_104796 -> Prop))). Qed.
Lemma lem4370725 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1774 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1816 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (MK_COMB (@lem4370724 _104796) (@lem4370723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370726 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) : (term1759 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') = (term1816 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'').
Proof. exact (TRANS (@lem4370654 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') (@lem4370725 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370727 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1761 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1817 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (fun_ext (fun f'' : type686 _104795 => @lem4370726 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'')). Qed.
Lemma lem4370728 {_104795 : Type'} : (@ex ((_104795 -> Prop) -> Prop)) = (@ex ((_104795 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104795 -> Prop) -> Prop))). Qed.
Lemma lem4370729 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1762 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1818 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370728 _104795) (@lem4370727 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370730 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') = (term1818 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2').
Proof. exact (TRANS (@lem4370634 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') (@lem4370729 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370731 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1749 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1819 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (fun_ext (fun t'' : _104758 -> Prop => @lem4370730 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2')). Qed.
Lemma lem4370732 {_104758 : Type'} : (@ex (_104758 -> Prop)) = (@ex (_104758 -> Prop)).
Proof. exact (eq_refl (@ex (_104758 -> Prop))). Qed.
Lemma lem4370733 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1750 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1820 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (MK_COMB (@lem4370732 _104758) (@lem4370731 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370734 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') = (term1820 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2').
Proof. exact (TRANS (@lem4370614 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') (@lem4370733 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370735 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1737 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1821 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (fun_ext (fun p2' : _104758 => @lem4370734 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2')). Qed.
Lemma lem4370736 {_104758 : Type'} : (@ex _104758) = (@ex _104758).
Proof. exact (eq_refl (@ex _104758)). Qed.
Lemma lem4370737 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1738 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1822 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (MK_COMB (@lem4370736 _104758) (@lem4370735 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370738 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) : (term1723 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') = (term1822 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1').
Proof. exact (TRANS (@lem4370594 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') (@lem4370737 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370739 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1725 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1823 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (fun_ext (fun p1' : _104757 => @lem4370738 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1')). Qed.
Lemma lem4370740 {_104757 : Type'} : (@ex _104757) = (@ex _104757).
Proof. exact (eq_refl (@ex _104757)). Qed.
Lemma lem4370741 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1726 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1824 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (MK_COMB (@lem4370740 _104757) (@lem4370739 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370742 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) : (term1711 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) = (term1824 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s).
Proof. exact (TRANS (@lem4370574 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) (@lem4370741 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370743 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1713 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1825 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (fun_ext (fun f' : type686 _104758 => @lem4370742 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s)). Qed.
Lemma lem4370744 {_104758 : Type'} : (@ex ((_104758 -> Prop) -> Prop)) = (@ex ((_104758 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104758 -> Prop) -> Prop))). Qed.
Lemma lem4370745 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1714 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1826 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (MK_COMB (@lem4370744 _104758) (@lem4370743 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370746 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) : (term1699 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) = (term1826 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s).
Proof. exact (TRANS (@lem4370554 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) (@lem4370745 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370747 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1701 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1827 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (fun_ext (fun s : _104757 -> Prop => @lem4370746 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s)). Qed.
Lemma lem4370748 {_104757 : Type'} : (@ex (_104757 -> Prop)) = (@ex (_104757 -> Prop)).
Proof. exact (eq_refl (@ex (_104757 -> Prop))). Qed.
Lemma lem4370749 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1702 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1828 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4370748 _104757) (@lem4370747 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370750 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1687 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) = (term1828 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2).
Proof. exact (TRANS (@lem4370534 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) (@lem4370749 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370751 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1689 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1829 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (fun_ext (fun t' : _104718 -> Prop => @lem4370750 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2)). Qed.
Lemma lem4370752 {_104718 : Type'} : (@ex (_104718 -> Prop)) = (@ex (_104718 -> Prop)).
Proof. exact (eq_refl (@ex (_104718 -> Prop))). Qed.
Lemma lem4370753 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1690 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1830 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (MK_COMB (@lem4370752 _104718) (@lem4370751 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370754 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1672 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) = (term1830 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2).
Proof. exact (TRANS (@lem4370514 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) (@lem4370753 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370755 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1674 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1831 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4370754 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2)). Qed.
Lemma lem4370756 {_104717 : Type'} : (@ex (_104717 -> Prop)) = (@ex (_104717 -> Prop)).
Proof. exact (eq_refl (@ex (_104717 -> Prop))). Qed.
Lemma lem4370757 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1675 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1832 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (MK_COMB (@lem4370756 _104717) (@lem4370755 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370758 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1657 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) = (term1832 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2).
Proof. exact (TRANS (@lem4370488 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) (@lem4370757 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370759 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1659 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1833 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (fun_ext (fun p2 : _104718 => @lem4370758 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2)). Qed.
Lemma lem4370760 {_104718 : Type'} : (@ex _104718) = (@ex _104718).
Proof. exact (eq_refl (@ex _104718)). Qed.
Lemma lem4370761 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1660 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1834 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (MK_COMB (@lem4370760 _104718) (@lem4370759 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370762 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) : (term1642 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) = (term1834 _104717 _104718 _104757 _104758 _104795 _104796 f g p1).
Proof. exact (TRANS (@lem4370462 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) (@lem4370761 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370763 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1644 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1835 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (fun_ext (fun p1 : _104717 => @lem4370762 _104717 _104718 _104757 _104758 _104795 _104796 f g p1)). Qed.
Lemma lem4370764 {_104717 : Type'} : (@ex _104717) = (@ex _104717).
Proof. exact (eq_refl (@ex _104717)). Qed.
Lemma lem4370765 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1645 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1836 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (MK_COMB (@lem4370764 _104717) (@lem4370763 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370766 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) : (term1627 _104717 _104718 _104757 _104758 _104795 _104796 f g) = (term1836 _104717 _104718 _104757 _104758 _104795 _104796 f g).
Proof. exact (TRANS (@lem4370436 _104717 _104718 _104757 _104758 _104795 _104796 f g) (@lem4370765 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370767 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1629 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1837 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (fun_ext (fun g : type686 _104718 => @lem4370766 _104717 _104718 _104757 _104758 _104795 _104796 f g)). Qed.
Lemma lem4370768 {_104718 : Type'} : (@ex ((_104718 -> Prop) -> Prop)) = (@ex ((_104718 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104718 -> Prop) -> Prop))). Qed.
Lemma lem4370769 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1630 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1838 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (MK_COMB (@lem4370768 _104718) (@lem4370767 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370770 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) : (term1612 _104717 _104718 _104757 _104758 _104795 _104796 f) = (term1838 _104717 _104718 _104757 _104758 _104795 _104796 f).
Proof. exact (TRANS (@lem4370410 _104717 _104718 _104757 _104758 _104795 _104796 f) (@lem4370769 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370771 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1614 _104717 _104718 _104757 _104758 _104795 _104796) = (term1839 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (fun_ext (fun f : type686 _104717 => @lem4370770 _104717 _104718 _104757 _104758 _104795 _104796 f)). Qed.
Lemma lem4370772 {_104717 : Type'} : (@ex ((_104717 -> Prop) -> Prop)) = (@ex ((_104717 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_104717 -> Prop) -> Prop))). Qed.
Lemma lem4370773 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1615 _104717 _104718 _104757 _104758 _104795 _104796) = (term1840 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (MK_COMB (@lem4370772 _104717) (@lem4370771 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370774 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term1600 _104717 _104718 _104757 _104758 _104795 _104796) = (term1840 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4370384 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370773 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370775 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term895 _104717 _104718 _104757 _104758 _104795 _104796) = (term1840 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4370358 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370774 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370776 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term627 _104717 _104718 _104757 _104758 _104795 _104796) = (term1840 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4369198 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370775 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370777 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : (term419 _104717 _104718 _104757 _104758 _104795 _104796) = (term1840 _104717 _104718 _104757 _104758 _104795 _104796).
Proof. exact (TRANS (@lem4365260 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4370776 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4370778 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : term1840 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4370777 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4364841 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4370779 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (h1 : term1838 _104717 _104718 _104757 _104758 _104795 _104796 f) : term1838 _104717 _104718 _104757 _104758 _104795 _104796 f.
Proof. exact (h1). Qed.
Lemma lem4370780 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (h1 : term1836 _104717 _104718 _104757 _104758 _104795 _104796 f g) : term1836 _104717 _104718 _104757 _104758 _104795 _104796 f g.
Proof. exact (h1). Qed.
Lemma lem4370781 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (h1 : term1834 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) : term1834 _104717 _104718 _104757 _104758 _104795 _104796 f g p1.
Proof. exact (h1). Qed.
Lemma lem4370782 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1832 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) : term1832 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4370783 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) (h1 : term1830 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) : term1830 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2.
Proof. exact (h1). Qed.
Lemma lem4370784 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1828 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) : term1828 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2.
Proof. exact (h1). Qed.
Lemma lem4370785 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) (h1 : term1826 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) : term1826 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s.
Proof. exact (h1). Qed.
Lemma lem4370786 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (h1 : term1824 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) : term1824 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s.
Proof. exact (h1). Qed.
Lemma lem4370787 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (h1 : term1822 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') : term1822 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1'.
Proof. exact (h1). Qed.
Lemma lem4370788 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1820 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') : term1820 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2'.
Proof. exact (h1). Qed.
Lemma lem4370789 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1818 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') : term1818 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2'.
Proof. exact (h1). Qed.
Lemma lem4370790 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (h1 : term1816 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') : term1816 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f''.
Proof. exact (h1). Qed.
Lemma lem4370791 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) (h1 : term1814 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') : term1814 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''.
Proof. exact (h1). Qed.
Lemma lem4370792 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (h1 : term1812 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') : term1812 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t'''.
Proof. exact (h1). Qed.
Lemma lem4370793 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') : term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4370794 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') : term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4370799 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370800 {_104796 : Type'} (f : _104796 -> Prop) (x : _104796) : (f x) = (@I (_104796 -> Prop) f x).
Proof. exact (@lem4370799 _104796 Prop f x). Qed.
Lemma lem4370802 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4370800 _104796 t''' p2''). Qed.
Lemma lem4370807 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370808 {_104795 : Type'} (f : _104795 -> Prop) (x : _104795) : (f x) = (@I (_104795 -> Prop) f x).
Proof. exact (@lem4370807 _104795 Prop f x). Qed.
Lemma lem4370810 {_104795 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) : (t'''' p1'') = (@I (_104795 -> Prop) t'''' p1'').
Proof. exact (@lem4370808 _104795 t'''' p1''). Qed.
Lemma lem4370811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370812 {_104795 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) : (term372 _104795 t'''' p1'') = (term1841 _104795 t'''' p1'').
Proof. exact (MK_COMB (@lem4370811) (@lem4370810 _104795 t'''' p1'')). Qed.
Lemma lem4370813 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term373 _104795 _104796 t'''' p1'' t''' p2'') = (term1842 _104795 _104796 t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370812 _104795 t'''' p1'') (@lem4370802 _104796 t''' p2'')). Qed.
Lemma lem4370818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370819 {_104795 : Type'} (f : type686 _104795) (x : _104795 -> Prop) : (f x) = (@I ((_104795 -> Prop) -> Prop) f x).
Proof. exact (@lem4370818 (_104795 -> Prop) Prop f x). Qed.
Lemma lem4370821 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (f'' t'''') = (@I ((_104795 -> Prop) -> Prop) f'' t'''').
Proof. exact (@lem4370819 _104795 f'' t''''). Qed.
Lemma lem4370822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370823 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (term359 _104795 f'' t'''') = (term1843 _104795 f'' t'''').
Proof. exact (MK_COMB (@lem4370822) (@lem4370821 _104795 f'' t'''')). Qed.
Lemma lem4370824 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term404 _104795 _104796 f'' t'''' p1'' t''' p2'') = (term1844 _104795 _104796 f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370823 _104795 f'' t'''') (@lem4370813 _104795 _104796 t'''' p1'' t''' p2'')). Qed.
Lemma lem4370825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370831 {_104796 : Type'} (f : _104796 -> Prop) (x : _104796) : (f x) = (@I (_104796 -> Prop) f x).
Proof. exact (@lem4370830 _104796 Prop f x). Qed.
Lemma lem4370833 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4370831 _104796 t''' p2''). Qed.
Lemma lem4370834 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (term565 _104796 t''' p2'') = (term1845 _104796 t''' p2'').
Proof. exact (MK_COMB (@lem4370825) (@lem4370833 _104796 t''' p2'')). Qed.
Lemma lem4370835 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370841 {_104795 : Type'} (f : _104795 -> Prop) (x : _104795) : (f x) = (@I (_104795 -> Prop) f x).
Proof. exact (@lem4370840 _104795 Prop f x). Qed.
Lemma lem4370843 {_104795 : Type'} (t : _104795 -> Prop) (p1'' : _104795) : (t p1'') = (@I (_104795 -> Prop) t p1'').
Proof. exact (@lem4370841 _104795 t p1''). Qed.
Lemma lem4370844 {_104795 : Type'} (t : _104795 -> Prop) (p1'' : _104795) : (term565 _104795 t p1'') = (term1845 _104795 t p1'').
Proof. exact (MK_COMB (@lem4370835) (@lem4370843 _104795 t p1'')). Qed.
Lemma lem4370845 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370850 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370851 {_104795 : Type'} (f : type686 _104795) (x : _104795 -> Prop) : (f x) = (@I ((_104795 -> Prop) -> Prop) f x).
Proof. exact (@lem4370850 (_104795 -> Prop) Prop f x). Qed.
Lemma lem4370853 {_104795 : Type'} (f'' : type686 _104795) (t : _104795 -> Prop) : (f'' t) = (@I ((_104795 -> Prop) -> Prop) f'' t).
Proof. exact (@lem4370851 _104795 f'' t). Qed.
Lemma lem4370854 {_104795 : Type'} (f'' : type686 _104795) (t : _104795 -> Prop) : (term1846 _104795 f'' t) = (term1847 _104795 f'' t).
Proof. exact (MK_COMB (@lem4370845) (@lem4370853 _104795 f'' t)). Qed.
Lemma lem4370855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370856 {_104795 : Type'} (f'' : type686 _104795) (t : _104795 -> Prop) : (term512 _104795 f'' t) = (term1848 _104795 f'' t).
Proof. exact (MK_COMB (@lem4370855) (@lem4370854 _104795 f'' t)). Qed.
Lemma lem4370857 {_104795 : Type'} (f'' : type686 _104795) (t : _104795 -> Prop) (p1'' : _104795) : (term426 _104795 f'' t p1'') = (term1849 _104795 f'' t p1'').
Proof. exact (MK_COMB (@lem4370856 _104795 f'' t) (@lem4370844 _104795 t p1'')). Qed.
Lemma lem4370858 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) : (term434 _104795 f'' p1'') = (term1850 _104795 f'' p1'').
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4370857 _104795 f'' t p1'')). Qed.
Lemma lem4370859 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4370860 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) : (term435 _104795 f'' p1'') = (term1851 _104795 f'' p1'').
Proof. exact (MK_COMB (@lem4370859 _104795) (@lem4370858 _104795 f'' p1'')). Qed.
Lemma lem4370861 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370862 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) : (term437 _104795 f'' p1'') = (term1852 _104795 f'' p1'').
Proof. exact (MK_COMB (@lem4370861) (@lem4370860 _104795 f'' p1'')). Qed.
Lemma lem4370863 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term567 _104795 _104796 f'' p1'' t''' p2'') = (term1853 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370862 _104795 f'' p1'') (@lem4370834 _104796 t''' p2'')). Qed.
Lemma lem4370864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370865 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term580 _104795 _104796 f'' p1'' t''' p2'') = (term1854 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370864) (@lem4370863 _104795 _104796 f'' p1'' t''' p2'')). Qed.
Lemma lem4370866 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1320 _104795 _104796 f'' t'''' p1'' t''' p2'') = (term1855 _104795 _104796 f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370865 _104795 _104796 f'' p1'' t''' p2'') (@lem4370824 _104795 _104796 f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4370867 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370872 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370873 {_104796 : Type'} (f : _104796 -> Prop) (x : _104796) : (f x) = (@I (_104796 -> Prop) f x).
Proof. exact (@lem4370872 _104796 Prop f x). Qed.
Lemma lem4370875 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4370873 _104796 t''' p2''). Qed.
Lemma lem4370876 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (term565 _104796 t''' p2'') = (term1845 _104796 t''' p2'').
Proof. exact (MK_COMB (@lem4370867) (@lem4370875 _104796 t''' p2'')). Qed.
Lemma lem4370877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370882 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370883 {_104795 : Type'} (f : _104795 -> Prop) (x : _104795) : (f x) = (@I (_104795 -> Prop) f x).
Proof. exact (@lem4370882 _104795 Prop f x). Qed.
Lemma lem4370885 {_104795 : Type'} (s : _104795 -> Prop) (p1'' : _104795) : (s p1'') = (@I (_104795 -> Prop) s p1'').
Proof. exact (@lem4370883 _104795 s p1''). Qed.
Lemma lem4370886 {_104795 : Type'} (s : _104795 -> Prop) (p1'' : _104795) : (term565 _104795 s p1'') = (term1845 _104795 s p1'').
Proof. exact (MK_COMB (@lem4370877) (@lem4370885 _104795 s p1'')). Qed.
Lemma lem4370887 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370888 {_104795 : Type'} (s : _104795 -> Prop) (p1'' : _104795) : (term508 _104795 s p1'') = (term1856 _104795 s p1'').
Proof. exact (MK_COMB (@lem4370887) (@lem4370886 _104795 s p1'')). Qed.
Lemma lem4370889 {_104795 _104796 : Type'} (s : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term444 _104795 _104796 s p1'' t''' p2'') = (term1857 _104795 _104796 s p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370888 _104795 s p1'') (@lem4370876 _104796 t''' p2'')). Qed.
Lemma lem4370890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370895 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370896 {_104795 : Type'} (f : type686 _104795) (x : _104795 -> Prop) : (f x) = (@I ((_104795 -> Prop) -> Prop) f x).
Proof. exact (@lem4370895 (_104795 -> Prop) Prop f x). Qed.
Lemma lem4370898 {_104795 : Type'} (f'' : type686 _104795) (s : _104795 -> Prop) : (f'' s) = (@I ((_104795 -> Prop) -> Prop) f'' s).
Proof. exact (@lem4370896 _104795 f'' s). Qed.
Lemma lem4370899 {_104795 : Type'} (f'' : type686 _104795) (s : _104795 -> Prop) : (term1846 _104795 f'' s) = (term1847 _104795 f'' s).
Proof. exact (MK_COMB (@lem4370890) (@lem4370898 _104795 f'' s)). Qed.
Lemma lem4370900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370901 {_104795 : Type'} (f'' : type686 _104795) (s : _104795 -> Prop) : (term512 _104795 f'' s) = (term1848 _104795 f'' s).
Proof. exact (MK_COMB (@lem4370900) (@lem4370899 _104795 f'' s)). Qed.
Lemma lem4370902 {_104795 _104796 : Type'} (f'' : type686 _104795) (s : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term570 _104795 _104796 f'' s p1'' t''' p2'') = (term1858 _104795 _104796 f'' s p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370901 _104795 f'' s) (@lem4370889 _104795 _104796 s p1'' t''' p2'')). Qed.
Lemma lem4370903 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term577 _104795 _104796 f'' p1'' t''' p2'') = (term1859 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4370902 _104795 _104796 f'' s p1'' t''' p2'')). Qed.
Lemma lem4370904 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4370905 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term578 _104795 _104796 f'' p1'' t''' p2'') = (term1860 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370904 _104795) (@lem4370903 _104795 _104796 f'' p1'' t''' p2'')). Qed.
Lemma lem4370910 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370911 {_104796 : Type'} (f : _104796 -> Prop) (x : _104796) : (f x) = (@I (_104796 -> Prop) f x).
Proof. exact (@lem4370910 _104796 Prop f x). Qed.
Lemma lem4370913 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4370911 _104796 t''' p2''). Qed.
Lemma lem4370918 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370919 {_104795 : Type'} (f : _104795 -> Prop) (x : _104795) : (f x) = (@I (_104795 -> Prop) f x).
Proof. exact (@lem4370918 _104795 Prop f x). Qed.
Lemma lem4370921 {_104795 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) : (t'''' p1'') = (@I (_104795 -> Prop) t'''' p1'').
Proof. exact (@lem4370919 _104795 t'''' p1''). Qed.
Lemma lem4370926 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370927 {_104795 : Type'} (f : type686 _104795) (x : _104795 -> Prop) : (f x) = (@I ((_104795 -> Prop) -> Prop) f x).
Proof. exact (@lem4370926 (_104795 -> Prop) Prop f x). Qed.
Lemma lem4370929 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (f'' t'''') = (@I ((_104795 -> Prop) -> Prop) f'' t'''').
Proof. exact (@lem4370927 _104795 f'' t''''). Qed.
Lemma lem4370930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370931 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (term359 _104795 f'' t'''') = (term1843 _104795 f'' t'''').
Proof. exact (MK_COMB (@lem4370930) (@lem4370929 _104795 f'' t'''')). Qed.
Lemma lem4370932 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) : (term361 _104795 f'' t'''' p1'') = (term1861 _104795 f'' t'''' p1'').
Proof. exact (MK_COMB (@lem4370931 _104795 f'' t'''') (@lem4370921 _104795 t'''' p1'')). Qed.
Lemma lem4370933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370934 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) : (term907 _104795 f'' t'''' p1'') = (term1862 _104795 f'' t'''' p1'').
Proof. exact (MK_COMB (@lem4370933) (@lem4370932 _104795 f'' t'''' p1'')). Qed.
Lemma lem4370935 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1283 _104795 _104796 f'' t'''' p1'' t''' p2'') = (term1863 _104795 _104796 f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370934 _104795 f'' t'''' p1'') (@lem4370913 _104796 t''' p2'')). Qed.
Lemma lem4370936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370937 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1298 _104795 _104796 f'' t'''' p1'' t''' p2'') = (term1864 _104795 _104796 f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370936) (@lem4370935 _104795 _104796 f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4370938 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1300 _104795 _104796 t'''' f'' p1'' t''' p2'') = (term1865 _104795 _104796 t'''' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370937 _104795 _104796 f'' t'''' p1'' t''' p2'') (@lem4370905 _104795 _104796 f'' p1'' t''' p2'')). Qed.
Lemma lem4370939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370940 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1417 _104795 _104796 t'''' f'' p1'' t''' p2'') = (term1866 _104795 _104796 t'''' f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370939) (@lem4370938 _104795 _104796 t'''' f'' p1'' t''' p2'')). Qed.
Lemma lem4370941 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1419 _104795 _104796 f'' t'''' p1'' t''' p2'') = (term1867 _104795 _104796 f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4370940 _104795 _104796 t'''' f'' p1'' t''' p2'') (@lem4370866 _104795 _104796 f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4370946 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370947 {_104758 : Type'} (f : _104758 -> Prop) (x : _104758) : (f x) = (@I (_104758 -> Prop) f x).
Proof. exact (@lem4370946 _104758 Prop f x). Qed.
Lemma lem4370949 {_104758 : Type'} (t'' : _104758 -> Prop) (p2' : _104758) : (t'' p2') = (@I (_104758 -> Prop) t'' p2').
Proof. exact (@lem4370947 _104758 t'' p2'). Qed.
Lemma lem4370954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370955 {_104757 : Type'} (f : _104757 -> Prop) (x : _104757) : (f x) = (@I (_104757 -> Prop) f x).
Proof. exact (@lem4370954 _104757 Prop f x). Qed.
Lemma lem4370957 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4370955 _104757 s p1'). Qed.
Lemma lem4370958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370959 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term372 _104757 s p1') = (term1841 _104757 s p1').
Proof. exact (MK_COMB (@lem4370958) (@lem4370957 _104757 s p1')). Qed.
Lemma lem4370960 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term373 _104757 _104758 s p1' t'' p2') = (term1842 _104757 _104758 s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370959 _104757 s p1') (@lem4370949 _104758 t'' p2')). Qed.
Lemma lem4370965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370966 {_104758 : Type'} (f : type686 _104758) (x : _104758 -> Prop) : (f x) = (@I ((_104758 -> Prop) -> Prop) f x).
Proof. exact (@lem4370965 (_104758 -> Prop) Prop f x). Qed.
Lemma lem4370968 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (f' t'') = (@I ((_104758 -> Prop) -> Prop) f' t'').
Proof. exact (@lem4370966 _104758 f' t''). Qed.
Lemma lem4370969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4370970 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (term359 _104758 f' t'') = (term1843 _104758 f' t'').
Proof. exact (MK_COMB (@lem4370969) (@lem4370968 _104758 f' t'')). Qed.
Lemma lem4370971 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term390 _104757 _104758 f' s p1' t'' p2') = (term1868 _104757 _104758 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4370970 _104758 f' t'') (@lem4370960 _104757 _104758 s p1' t'' p2')). Qed.
Lemma lem4370972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370977 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370978 {_104758 : Type'} (f : _104758 -> Prop) (x : _104758) : (f x) = (@I (_104758 -> Prop) f x).
Proof. exact (@lem4370977 _104758 Prop f x). Qed.
Lemma lem4370980 {_104758 : Type'} (t : _104758 -> Prop) (p2' : _104758) : (t p2') = (@I (_104758 -> Prop) t p2').
Proof. exact (@lem4370978 _104758 t p2'). Qed.
Lemma lem4370981 {_104758 : Type'} (t : _104758 -> Prop) (p2' : _104758) : (term565 _104758 t p2') = (term1845 _104758 t p2').
Proof. exact (MK_COMB (@lem4370972) (@lem4370980 _104758 t p2')). Qed.
Lemma lem4370982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4370987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4370988 {_104758 : Type'} (f : type686 _104758) (x : _104758 -> Prop) : (f x) = (@I ((_104758 -> Prop) -> Prop) f x).
Proof. exact (@lem4370987 (_104758 -> Prop) Prop f x). Qed.
Lemma lem4370990 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (f' t) = (@I ((_104758 -> Prop) -> Prop) f' t).
Proof. exact (@lem4370988 _104758 f' t). Qed.
Lemma lem4370991 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (term1846 _104758 f' t) = (term1847 _104758 f' t).
Proof. exact (MK_COMB (@lem4370982) (@lem4370990 _104758 f' t)). Qed.
Lemma lem4370992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4370993 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (term512 _104758 f' t) = (term1848 _104758 f' t).
Proof. exact (MK_COMB (@lem4370992) (@lem4370991 _104758 f' t)). Qed.
Lemma lem4370994 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) (p2' : _104758) : (term426 _104758 f' t p2') = (term1849 _104758 f' t p2').
Proof. exact (MK_COMB (@lem4370993 _104758 f' t) (@lem4370981 _104758 t p2')). Qed.
Lemma lem4370995 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) : (term434 _104758 f' p2') = (term1850 _104758 f' p2').
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4370994 _104758 f' t p2')). Qed.
Lemma lem4370996 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4370997 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) : (term435 _104758 f' p2') = (term1851 _104758 f' p2').
Proof. exact (MK_COMB (@lem4370996 _104758) (@lem4370995 _104758 f' p2')). Qed.
Lemma lem4370998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371004 {_104757 : Type'} (f : _104757 -> Prop) (x : _104757) : (f x) = (@I (_104757 -> Prop) f x).
Proof. exact (@lem4371003 _104757 Prop f x). Qed.
Lemma lem4371006 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4371004 _104757 s p1'). Qed.
Lemma lem4371007 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term565 _104757 s p1') = (term1845 _104757 s p1').
Proof. exact (MK_COMB (@lem4370998) (@lem4371006 _104757 s p1')). Qed.
Lemma lem4371008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371009 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term508 _104757 s p1') = (term1856 _104757 s p1').
Proof. exact (MK_COMB (@lem4371008) (@lem4371007 _104757 s p1')). Qed.
Lemma lem4371010 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (f' : type686 _104758) (p2' : _104758) : (term510 _104757 _104758 s p1' f' p2') = (term1869 _104757 _104758 s p1' f' p2').
Proof. exact (MK_COMB (@lem4371009 _104757 s p1') (@lem4370997 _104758 f' p2')). Qed.
Lemma lem4371011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371012 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (f' : type686 _104758) (p2' : _104758) : (term524 _104757 _104758 s p1' f' p2') = (term1870 _104757 _104758 s p1' f' p2').
Proof. exact (MK_COMB (@lem4371011) (@lem4371010 _104757 _104758 s p1' f' p2')). Qed.
Lemma lem4371013 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1167 _104757 _104758 f' s p1' t'' p2') = (term1871 _104757 _104758 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4371012 _104757 _104758 s p1' f' p2') (@lem4370971 _104757 _104758 f' s p1' t'' p2')). Qed.
Lemma lem4371014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371020 {_104758 : Type'} (f : _104758 -> Prop) (x : _104758) : (f x) = (@I (_104758 -> Prop) f x).
Proof. exact (@lem4371019 _104758 Prop f x). Qed.
Lemma lem4371022 {_104758 : Type'} (t : _104758 -> Prop) (p2' : _104758) : (t p2') = (@I (_104758 -> Prop) t p2').
Proof. exact (@lem4371020 _104758 t p2'). Qed.
Lemma lem4371023 {_104758 : Type'} (t : _104758 -> Prop) (p2' : _104758) : (term565 _104758 t p2') = (term1845 _104758 t p2').
Proof. exact (MK_COMB (@lem4371014) (@lem4371022 _104758 t p2')). Qed.
Lemma lem4371024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371029 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371030 {_104757 : Type'} (f : _104757 -> Prop) (x : _104757) : (f x) = (@I (_104757 -> Prop) f x).
Proof. exact (@lem4371029 _104757 Prop f x). Qed.
Lemma lem4371032 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4371030 _104757 s p1'). Qed.
Lemma lem4371033 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term565 _104757 s p1') = (term1845 _104757 s p1').
Proof. exact (MK_COMB (@lem4371024) (@lem4371032 _104757 s p1')). Qed.
Lemma lem4371034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371035 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term508 _104757 s p1') = (term1856 _104757 s p1').
Proof. exact (MK_COMB (@lem4371034) (@lem4371033 _104757 s p1')). Qed.
Lemma lem4371036 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (t : _104758 -> Prop) (p2' : _104758) : (term444 _104757 _104758 s p1' t p2') = (term1857 _104757 _104758 s p1' t p2').
Proof. exact (MK_COMB (@lem4371035 _104757 s p1') (@lem4371023 _104758 t p2')). Qed.
Lemma lem4371037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371042 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371043 {_104758 : Type'} (f : type686 _104758) (x : _104758 -> Prop) : (f x) = (@I ((_104758 -> Prop) -> Prop) f x).
Proof. exact (@lem4371042 (_104758 -> Prop) Prop f x). Qed.
Lemma lem4371045 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (f' t) = (@I ((_104758 -> Prop) -> Prop) f' t).
Proof. exact (@lem4371043 _104758 f' t). Qed.
Lemma lem4371046 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (term1846 _104758 f' t) = (term1847 _104758 f' t).
Proof. exact (MK_COMB (@lem4371037) (@lem4371045 _104758 f' t)). Qed.
Lemma lem4371047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371048 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) : (term512 _104758 f' t) = (term1848 _104758 f' t).
Proof. exact (MK_COMB (@lem4371047) (@lem4371046 _104758 f' t)). Qed.
Lemma lem4371049 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t : _104758 -> Prop) (p2' : _104758) : (term514 _104757 _104758 f' s p1' t p2') = (term1872 _104757 _104758 f' s p1' t p2').
Proof. exact (MK_COMB (@lem4371048 _104758 f' t) (@lem4371036 _104757 _104758 s p1' t p2')). Qed.
Lemma lem4371050 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term521 _104757 _104758 f' s p1' p2') = (term1873 _104757 _104758 f' s p1' p2').
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4371049 _104757 _104758 f' s p1' t p2')). Qed.
Lemma lem4371051 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4371052 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term522 _104757 _104758 f' s p1' p2') = (term1874 _104757 _104758 f' s p1' p2').
Proof. exact (MK_COMB (@lem4371051 _104758) (@lem4371050 _104757 _104758 f' s p1' p2')). Qed.
Lemma lem4371057 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371058 {_104758 : Type'} (f : _104758 -> Prop) (x : _104758) : (f x) = (@I (_104758 -> Prop) f x).
Proof. exact (@lem4371057 _104758 Prop f x). Qed.
Lemma lem4371060 {_104758 : Type'} (t'' : _104758 -> Prop) (p2' : _104758) : (t'' p2') = (@I (_104758 -> Prop) t'' p2').
Proof. exact (@lem4371058 _104758 t'' p2'). Qed.
Lemma lem4371065 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371066 {_104758 : Type'} (f : type686 _104758) (x : _104758 -> Prop) : (f x) = (@I ((_104758 -> Prop) -> Prop) f x).
Proof. exact (@lem4371065 (_104758 -> Prop) Prop f x). Qed.
Lemma lem4371068 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (f' t'') = (@I ((_104758 -> Prop) -> Prop) f' t'').
Proof. exact (@lem4371066 _104758 f' t''). Qed.
Lemma lem4371069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371070 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (term359 _104758 f' t'') = (term1843 _104758 f' t'').
Proof. exact (MK_COMB (@lem4371069) (@lem4371068 _104758 f' t'')). Qed.
Lemma lem4371071 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) (p2' : _104758) : (term361 _104758 f' t'' p2') = (term1861 _104758 f' t'' p2').
Proof. exact (MK_COMB (@lem4371070 _104758 f' t'') (@lem4371060 _104758 t'' p2')). Qed.
Lemma lem4371076 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371077 {_104757 : Type'} (f : _104757 -> Prop) (x : _104757) : (f x) = (@I (_104757 -> Prop) f x).
Proof. exact (@lem4371076 _104757 Prop f x). Qed.
Lemma lem4371079 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4371077 _104757 s p1'). Qed.
Lemma lem4371080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371081 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term372 _104757 s p1') = (term1841 _104757 s p1').
Proof. exact (MK_COMB (@lem4371080) (@lem4371079 _104757 s p1')). Qed.
Lemma lem4371082 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (f' : type686 _104758) (t'' : _104758 -> Prop) (p2' : _104758) : (term1130 _104757 _104758 s p1' f' t'' p2') = (term1875 _104757 _104758 s p1' f' t'' p2').
Proof. exact (MK_COMB (@lem4371081 _104757 s p1') (@lem4371071 _104758 f' t'' p2')). Qed.
Lemma lem4371083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371084 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (f' : type686 _104758) (t'' : _104758 -> Prop) (p2' : _104758) : (term1145 _104757 _104758 s p1' f' t'' p2') = (term1876 _104757 _104758 s p1' f' t'' p2').
Proof. exact (MK_COMB (@lem4371083) (@lem4371082 _104757 _104758 s p1' f' t'' p2')). Qed.
Lemma lem4371085 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1147 _104757 _104758 t'' f' s p1' p2') = (term1877 _104757 _104758 t'' f' s p1' p2').
Proof. exact (MK_COMB (@lem4371084 _104757 _104758 s p1' f' t'' p2') (@lem4371052 _104757 _104758 f' s p1' p2')). Qed.
Lemma lem4371086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371087 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1264 _104757 _104758 t'' f' s p1' p2') = (term1878 _104757 _104758 t'' f' s p1' p2').
Proof. exact (MK_COMB (@lem4371086) (@lem4371085 _104757 _104758 t'' f' s p1' p2')). Qed.
Lemma lem4371088 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1266 _104757 _104758 f' s p1' t'' p2') = (term1879 _104757 _104758 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4371087 _104757 _104758 t'' f' s p1' p2') (@lem4371013 _104757 _104758 f' s p1' t'' p2')). Qed.
Lemma lem4371089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371090 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) : (term1510 _104757 _104758 f' s p1' t'' p2') = (term1880 _104757 _104758 f' s p1' t'' p2').
Proof. exact (MK_COMB (@lem4371089) (@lem4371088 _104757 _104758 f' s p1' t'' p2')). Qed.
Lemma lem4371091 {_104757 _104758 _104795 _104796 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1578 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') = (term1881 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4371090 _104757 _104758 f' s p1' t'' p2') (@lem4370941 _104795 _104796 f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4371096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371097 {_104718 : Type'} (f : _104718 -> Prop) (x : _104718) : (f x) = (@I (_104718 -> Prop) f x).
Proof. exact (@lem4371096 _104718 Prop f x). Qed.
Lemma lem4371099 {_104718 : Type'} (t' : _104718 -> Prop) (p2 : _104718) : (t' p2) = (@I (_104718 -> Prop) t' p2).
Proof. exact (@lem4371097 _104718 t' p2). Qed.
Lemma lem4371104 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371105 {_104717 : Type'} (f : _104717 -> Prop) (x : _104717) : (f x) = (@I (_104717 -> Prop) f x).
Proof. exact (@lem4371104 _104717 Prop f x). Qed.
Lemma lem4371107 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (t p1) = (@I (_104717 -> Prop) t p1).
Proof. exact (@lem4371105 _104717 t p1). Qed.
Lemma lem4371108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371109 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (term372 _104717 t p1) = (term1841 _104717 t p1).
Proof. exact (MK_COMB (@lem4371108) (@lem4371107 _104717 t p1)). Qed.
Lemma lem4371110 {_104717 _104718 : Type'} (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term373 _104717 _104718 t p1 t' p2) = (term1842 _104717 _104718 t p1 t' p2).
Proof. exact (MK_COMB (@lem4371109 _104717 t p1) (@lem4371099 _104718 t' p2)). Qed.
Lemma lem4371115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371116 {_104718 : Type'} (f : type686 _104718) (x : _104718 -> Prop) : (f x) = (@I ((_104718 -> Prop) -> Prop) f x).
Proof. exact (@lem4371115 (_104718 -> Prop) Prop f x). Qed.
Lemma lem4371118 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) : (g t') = (@I ((_104718 -> Prop) -> Prop) g t').
Proof. exact (@lem4371116 _104718 g t'). Qed.
Lemma lem4371123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371124 {_104717 : Type'} (f : type686 _104717) (x : _104717 -> Prop) : (f x) = (@I ((_104717 -> Prop) -> Prop) f x).
Proof. exact (@lem4371123 (_104717 -> Prop) Prop f x). Qed.
Lemma lem4371126 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (f t) = (@I ((_104717 -> Prop) -> Prop) f t).
Proof. exact (@lem4371124 _104717 f t). Qed.
Lemma lem4371127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371128 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term359 _104717 f t) = (term1843 _104717 f t).
Proof. exact (MK_COMB (@lem4371127) (@lem4371126 _104717 f t)). Qed.
Lemma lem4371129 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (g : type686 _104718) (t' : _104718 -> Prop) : (term369 _104717 _104718 f t g t') = (term1882 _104717 _104718 f t g t').
Proof. exact (MK_COMB (@lem4371128 _104717 f t) (@lem4371118 _104718 g t')). Qed.
Lemma lem4371130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371131 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (g : type686 _104718) (t' : _104718 -> Prop) : (term370 _104717 _104718 f t g t') = (term1883 _104717 _104718 f t g t').
Proof. exact (MK_COMB (@lem4371130) (@lem4371129 _104717 _104718 f t g t')). Qed.
Lemma lem4371132 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term374 _104717 _104718 f g t p1 t' p2) = (term1884 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4371131 _104717 _104718 f t g t') (@lem4371110 _104717 _104718 t p1 t' p2)). Qed.
Lemma lem4371133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371138 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371139 {_104718 : Type'} (f : _104718 -> Prop) (x : _104718) : (f x) = (@I (_104718 -> Prop) f x).
Proof. exact (@lem4371138 _104718 Prop f x). Qed.
Lemma lem4371141 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (t p2) = (@I (_104718 -> Prop) t p2).
Proof. exact (@lem4371139 _104718 t p2). Qed.
Lemma lem4371142 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (term565 _104718 t p2) = (term1845 _104718 t p2).
Proof. exact (MK_COMB (@lem4371133) (@lem4371141 _104718 t p2)). Qed.
Lemma lem4371143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371148 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371149 {_104718 : Type'} (f : type686 _104718) (x : _104718 -> Prop) : (f x) = (@I ((_104718 -> Prop) -> Prop) f x).
Proof. exact (@lem4371148 (_104718 -> Prop) Prop f x). Qed.
Lemma lem4371151 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (g t) = (@I ((_104718 -> Prop) -> Prop) g t).
Proof. exact (@lem4371149 _104718 g t). Qed.
Lemma lem4371152 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (term1846 _104718 g t) = (term1847 _104718 g t).
Proof. exact (MK_COMB (@lem4371143) (@lem4371151 _104718 g t)). Qed.
Lemma lem4371153 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371154 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (term512 _104718 g t) = (term1848 _104718 g t).
Proof. exact (MK_COMB (@lem4371153) (@lem4371152 _104718 g t)). Qed.
Lemma lem4371155 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term426 _104718 g t p2) = (term1849 _104718 g t p2).
Proof. exact (MK_COMB (@lem4371154 _104718 g t) (@lem4371142 _104718 t p2)). Qed.
Lemma lem4371156 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term434 _104718 g p2) = (term1850 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4371155 _104718 g t p2)). Qed.
Lemma lem4371157 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4371158 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term435 _104718 g p2) = (term1851 _104718 g p2).
Proof. exact (MK_COMB (@lem4371157 _104718) (@lem4371156 _104718 g p2)). Qed.
Lemma lem4371159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371165 {_104717 : Type'} (f : _104717 -> Prop) (x : _104717) : (f x) = (@I (_104717 -> Prop) f x).
Proof. exact (@lem4371164 _104717 Prop f x). Qed.
Lemma lem4371167 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (t p1) = (@I (_104717 -> Prop) t p1).
Proof. exact (@lem4371165 _104717 t p1). Qed.
Lemma lem4371168 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (term565 _104717 t p1) = (term1845 _104717 t p1).
Proof. exact (MK_COMB (@lem4371159) (@lem4371167 _104717 t p1)). Qed.
Lemma lem4371169 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371174 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371175 {_104717 : Type'} (f : type686 _104717) (x : _104717 -> Prop) : (f x) = (@I ((_104717 -> Prop) -> Prop) f x).
Proof. exact (@lem4371174 (_104717 -> Prop) Prop f x). Qed.
Lemma lem4371177 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (f t) = (@I ((_104717 -> Prop) -> Prop) f t).
Proof. exact (@lem4371175 _104717 f t). Qed.
Lemma lem4371178 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term1846 _104717 f t) = (term1847 _104717 f t).
Proof. exact (MK_COMB (@lem4371169) (@lem4371177 _104717 f t)). Qed.
Lemma lem4371179 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371180 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term512 _104717 f t) = (term1848 _104717 f t).
Proof. exact (MK_COMB (@lem4371179) (@lem4371178 _104717 f t)). Qed.
Lemma lem4371181 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term426 _104717 f t p1) = (term1849 _104717 f t p1).
Proof. exact (MK_COMB (@lem4371180 _104717 f t) (@lem4371168 _104717 t p1)). Qed.
Lemma lem4371182 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term434 _104717 f p1) = (term1850 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4371181 _104717 f t p1)). Qed.
Lemma lem4371183 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4371184 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term435 _104717 f p1) = (term1851 _104717 f p1).
Proof. exact (MK_COMB (@lem4371183 _104717) (@lem4371182 _104717 f p1)). Qed.
Lemma lem4371185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371186 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term437 _104717 f p1) = (term1852 _104717 f p1).
Proof. exact (MK_COMB (@lem4371185) (@lem4371184 _104717 f p1)). Qed.
Lemma lem4371187 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term439 _104717 _104718 f p1 g p2) = (term1885 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4371186 _104717 f p1) (@lem4371158 _104718 g p2)). Qed.
Lemma lem4371188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371189 {_104717 _104718 : Type'} (f : type686 _104717) (p1 : _104717) (g : type686 _104718) (p2 : _104718) : (term465 _104717 _104718 f p1 g p2) = (term1886 _104717 _104718 f p1 g p2).
Proof. exact (MK_COMB (@lem4371188) (@lem4371187 _104717 _104718 f p1 g p2)). Qed.
Lemma lem4371190 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term989 _104717 _104718 f g t p1 t' p2) = (term1887 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4371189 _104717 _104718 f p1 g p2) (@lem4371132 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4371191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371197 {_104718 : Type'} (f : _104718 -> Prop) (x : _104718) : (f x) = (@I (_104718 -> Prop) f x).
Proof. exact (@lem4371196 _104718 Prop f x). Qed.
Lemma lem4371199 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (t p2) = (@I (_104718 -> Prop) t p2).
Proof. exact (@lem4371197 _104718 t p2). Qed.
Lemma lem4371200 {_104718 : Type'} (t : _104718 -> Prop) (p2 : _104718) : (term565 _104718 t p2) = (term1845 _104718 t p2).
Proof. exact (MK_COMB (@lem4371191) (@lem4371199 _104718 t p2)). Qed.
Lemma lem4371201 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371207 {_104717 : Type'} (f : _104717 -> Prop) (x : _104717) : (f x) = (@I (_104717 -> Prop) f x).
Proof. exact (@lem4371206 _104717 Prop f x). Qed.
Lemma lem4371209 {_104717 : Type'} (s : _104717 -> Prop) (p1 : _104717) : (s p1) = (@I (_104717 -> Prop) s p1).
Proof. exact (@lem4371207 _104717 s p1). Qed.
Lemma lem4371210 {_104717 : Type'} (s : _104717 -> Prop) (p1 : _104717) : (term565 _104717 s p1) = (term1845 _104717 s p1).
Proof. exact (MK_COMB (@lem4371201) (@lem4371209 _104717 s p1)). Qed.
Lemma lem4371211 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371212 {_104717 : Type'} (s : _104717 -> Prop) (p1 : _104717) : (term508 _104717 s p1) = (term1856 _104717 s p1).
Proof. exact (MK_COMB (@lem4371211) (@lem4371210 _104717 s p1)). Qed.
Lemma lem4371213 {_104717 _104718 : Type'} (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term444 _104717 _104718 s p1 t p2) = (term1857 _104717 _104718 s p1 t p2).
Proof. exact (MK_COMB (@lem4371212 _104717 s p1) (@lem4371200 _104718 t p2)). Qed.
Lemma lem4371214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371220 {_104718 : Type'} (f : type686 _104718) (x : _104718 -> Prop) : (f x) = (@I ((_104718 -> Prop) -> Prop) f x).
Proof. exact (@lem4371219 (_104718 -> Prop) Prop f x). Qed.
Lemma lem4371222 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (g t) = (@I ((_104718 -> Prop) -> Prop) g t).
Proof. exact (@lem4371220 _104718 g t). Qed.
Lemma lem4371223 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) : (term1846 _104718 g t) = (term1847 _104718 g t).
Proof. exact (MK_COMB (@lem4371214) (@lem4371222 _104718 g t)). Qed.
Lemma lem4371224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4371229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371230 {_104717 : Type'} (f : type686 _104717) (x : _104717 -> Prop) : (f x) = (@I ((_104717 -> Prop) -> Prop) f x).
Proof. exact (@lem4371229 (_104717 -> Prop) Prop f x). Qed.
Lemma lem4371232 {_104717 : Type'} (f : type686 _104717) (s : _104717 -> Prop) : (f s) = (@I ((_104717 -> Prop) -> Prop) f s).
Proof. exact (@lem4371230 _104717 f s). Qed.
Lemma lem4371233 {_104717 : Type'} (f : type686 _104717) (s : _104717 -> Prop) : (term1846 _104717 f s) = (term1847 _104717 f s).
Proof. exact (MK_COMB (@lem4371224) (@lem4371232 _104717 f s)). Qed.
Lemma lem4371234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371235 {_104717 : Type'} (f : type686 _104717) (s : _104717 -> Prop) : (term512 _104717 f s) = (term1848 _104717 f s).
Proof. exact (MK_COMB (@lem4371234) (@lem4371233 _104717 f s)). Qed.
Lemma lem4371236 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term442 _104717 _104718 f s g t) = (term1888 _104717 _104718 f s g t).
Proof. exact (MK_COMB (@lem4371235 _104717 f s) (@lem4371223 _104718 g t)). Qed.
Lemma lem4371237 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371238 {_104717 _104718 : Type'} (f : type686 _104717) (s : _104717 -> Prop) (g : type686 _104718) (t : _104718 -> Prop) : (term446 _104717 _104718 f s g t) = (term1889 _104717 _104718 f s g t).
Proof. exact (MK_COMB (@lem4371237) (@lem4371236 _104717 _104718 f s g t)). Qed.
Lemma lem4371239 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term448 _104717 _104718 f g s p1 t p2) = (term1890 _104717 _104718 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4371238 _104717 _104718 f s g t) (@lem4371213 _104717 _104718 s p1 t p2)). Qed.
Lemma lem4371240 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term455 _104717 _104718 f g s p1 p2) = (term1891 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4371239 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4371241 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4371242 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term456 _104717 _104718 f g s p1 p2) = (term1892 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4371241 _104718) (@lem4371240 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4371243 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term462 _104717 _104718 f g p1 p2) = (term1893 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4371242 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4371244 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4371245 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term463 _104717 _104718 f g p1 p2) = (term1894 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4371244 _104717) (@lem4371243 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4371250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371251 {_104718 : Type'} (f : _104718 -> Prop) (x : _104718) : (f x) = (@I (_104718 -> Prop) f x).
Proof. exact (@lem4371250 _104718 Prop f x). Qed.
Lemma lem4371253 {_104718 : Type'} (t' : _104718 -> Prop) (p2 : _104718) : (t' p2) = (@I (_104718 -> Prop) t' p2).
Proof. exact (@lem4371251 _104718 t' p2). Qed.
Lemma lem4371258 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371259 {_104718 : Type'} (f : type686 _104718) (x : _104718 -> Prop) : (f x) = (@I ((_104718 -> Prop) -> Prop) f x).
Proof. exact (@lem4371258 (_104718 -> Prop) Prop f x). Qed.
Lemma lem4371261 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) : (g t') = (@I ((_104718 -> Prop) -> Prop) g t').
Proof. exact (@lem4371259 _104718 g t'). Qed.
Lemma lem4371262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371263 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) : (term359 _104718 g t') = (term1843 _104718 g t').
Proof. exact (MK_COMB (@lem4371262) (@lem4371261 _104718 g t')). Qed.
Lemma lem4371264 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term361 _104718 g t' p2) = (term1861 _104718 g t' p2).
Proof. exact (MK_COMB (@lem4371263 _104718 g t') (@lem4371253 _104718 t' p2)). Qed.
Lemma lem4371269 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371270 {_104717 : Type'} (f : _104717 -> Prop) (x : _104717) : (f x) = (@I (_104717 -> Prop) f x).
Proof. exact (@lem4371269 _104717 Prop f x). Qed.
Lemma lem4371272 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (t p1) = (@I (_104717 -> Prop) t p1).
Proof. exact (@lem4371270 _104717 t p1). Qed.
Lemma lem4371277 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4371278 {_104717 : Type'} (f : type686 _104717) (x : _104717 -> Prop) : (f x) = (@I ((_104717 -> Prop) -> Prop) f x).
Proof. exact (@lem4371277 (_104717 -> Prop) Prop f x). Qed.
Lemma lem4371280 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (f t) = (@I ((_104717 -> Prop) -> Prop) f t).
Proof. exact (@lem4371278 _104717 f t). Qed.
Lemma lem4371281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371282 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term359 _104717 f t) = (term1843 _104717 f t).
Proof. exact (MK_COMB (@lem4371281) (@lem4371280 _104717 f t)). Qed.
Lemma lem4371283 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term361 _104717 f t p1) = (term1861 _104717 f t p1).
Proof. exact (MK_COMB (@lem4371282 _104717 f t) (@lem4371272 _104717 t p1)). Qed.
Lemma lem4371284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371285 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term907 _104717 f t p1) = (term1862 _104717 f t p1).
Proof. exact (MK_COMB (@lem4371284) (@lem4371283 _104717 f t p1)). Qed.
Lemma lem4371286 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term922 _104717 _104718 f t p1 g t' p2) = (term1895 _104717 _104718 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4371285 _104717 f t p1) (@lem4371264 _104718 g t' p2)). Qed.
Lemma lem4371287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4371288 {_104717 _104718 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) (g : type686 _104718) (t' : _104718 -> Prop) (p2 : _104718) : (term954 _104717 _104718 f t p1 g t' p2) = (term1896 _104717 _104718 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4371287) (@lem4371286 _104717 _104718 f t p1 g t' p2)). Qed.
Lemma lem4371289 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term956 _104717 _104718 t t' f g p1 p2) = (term1897 _104717 _104718 t t' f g p1 p2).
Proof. exact (MK_COMB (@lem4371288 _104717 _104718 f t p1 g t' p2) (@lem4371245 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4371290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371291 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1109 _104717 _104718 t t' f g p1 p2) = (term1898 _104717 _104718 t t' f g p1 p2).
Proof. exact (MK_COMB (@lem4371290) (@lem4371289 _104717 _104718 t t' f g p1 p2)). Qed.
Lemma lem4371292 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1111 _104717 _104718 f g t p1 t' p2) = (term1899 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4371291 _104717 _104718 t t' f g p1 p2) (@lem4371190 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4371293 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4371294 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) : (term1685 _104717 _104718 f g t p1 t' p2) = (term1900 _104717 _104718 f g t p1 t' p2).
Proof. exact (MK_COMB (@lem4371293) (@lem4371292 _104717 _104718 f g t p1 t' p2)). Qed.
Lemma lem4371295 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') = (term1901 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4371294 _104717 _104718 f g t p1 t' p2) (@lem4371091 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'')). Qed.
Lemma lem4371296 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') : term1901 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2''.
Proof. exact (EQ_MP (@lem4371295 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') (@lem4370794 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4371297 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1899 _104717 _104718 f g t p1 t' p2) : term1899 _104717 _104718 f g t p1 t' p2.
Proof. exact (h1). Qed.
Lemma lem4371298 {_104757 _104758 _104795 _104796 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1881 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') : term1881 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371299 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1897 _104717 _104718 t t' f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4371300 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1887 _104717 _104718 f g t p1 t' p2.
Proof. exact (h1). Qed.
Lemma lem4371301 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1894 _104717 _104718 f g p1 p2.
Proof. exact (proj2 (@lem4371299 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371302 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1895 _104717 _104718 f t p1 g t' p2.
Proof. exact (proj1 (@lem4371299 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371303 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1861 _104718 g t' p2.
Proof. exact (proj2 (@lem4371302 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371304 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1861 _104717 f t p1.
Proof. exact (proj1 (@lem4371302 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371309 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1884 _104717 _104718 f g t p1 t' p2.
Proof. exact (proj2 (@lem4371300 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371310 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1885 _104717 _104718 f p1 g p2.
Proof. exact (proj1 (@lem4371300 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371311 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1842 _104717 _104718 t p1 t' p2.
Proof. exact (proj2 (@lem4371309 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371312 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1882 _104717 _104718 f t g t'.
Proof. exact (proj1 (@lem4371309 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371317 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1851 _104717 f p1.
Proof. exact (h1). Qed.
Lemma lem4371318 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1851 _104718 g p2.
Proof. exact (h1). Qed.
Lemma lem4371319 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1879 _104757 _104758 f' s p1' t'' p2') : term1879 _104757 _104758 f' s p1' t'' p2'.
Proof. exact (h1). Qed.
Lemma lem4371320 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1867 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1867 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371321 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1877 _104757 _104758 t'' f' s p1' p2'.
Proof. exact (h1). Qed.
Lemma lem4371322 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1871 _104757 _104758 f' s p1' t'' p2'.
Proof. exact (h1). Qed.
Lemma lem4371323 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1874 _104757 _104758 f' s p1' p2'.
Proof. exact (proj2 (@lem4371321 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371324 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1875 _104757 _104758 s p1' f' t'' p2'.
Proof. exact (proj1 (@lem4371321 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371325 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1861 _104758 f' t'' p2'.
Proof. exact (proj2 (@lem4371324 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371329 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1868 _104757 _104758 f' s p1' t'' p2'.
Proof. exact (proj2 (@lem4371322 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371330 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1869 _104757 _104758 s p1' f' p2'.
Proof. exact (proj1 (@lem4371322 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371331 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1842 _104757 _104758 s p1' t'' p2'.
Proof. exact (proj2 (@lem4371329 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371336 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1851 _104758 f' p2'.
Proof. exact (h1). Qed.
Lemma lem4371337 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1865 _104795 _104796 t'''' f'' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371338 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1855 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371339 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1860 _104795 _104796 f'' p1'' t''' p2''.
Proof. exact (proj2 (@lem4371337 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371340 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1863 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (proj1 (@lem4371337 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371342 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1861 _104795 f'' t'''' p1''.
Proof. exact (proj1 (@lem4371340 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371345 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1844 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (proj2 (@lem4371338 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4371346 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1853 _104795 _104796 f'' p1'' t''' p2''.
Proof. exact (proj1 (@lem4371338 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4371347 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1842 _104795 _104796 t'''' p1'' t''' p2''.
Proof. exact (proj2 (@lem4371345 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4371351 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1851 _104795 f'' p1''.
Proof. exact (h1). Qed.
Lemma lem4371372 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (t : _104718 -> Prop) (p2 : _104718) : (term1890 _104717 _104718 f g s p1 t p2) = (term1890 _104717 _104718 f g s p1 t p2).
Proof. exact (eq_refl (term1890 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4371373 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1891 _104717 _104718 f g s p1 p2) = (term1891 _104717 _104718 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4371372 _104717 _104718 f g s p1 t p2)). Qed.
Lemma lem4371374 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4371375 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (s : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1892 _104717 _104718 f g s p1 p2) = (term1892 _104717 _104718 f g s p1 p2).
Proof. exact (MK_COMB (@lem4371374 _104718) (@lem4371373 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4371376 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1893 _104717 _104718 f g p1 p2) = (term1893 _104717 _104718 f g p1 p2).
Proof. exact (fun_ext (fun s : _104717 -> Prop => @lem4371375 _104717 _104718 f g s p1 p2)). Qed.
Lemma lem4371377 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4371379 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) : (term1894 _104717 _104718 f g p1 p2) = (term1894 _104717 _104718 f g p1 p2).
Proof. exact (MK_COMB (@lem4371377 _104717) (@lem4371376 _104717 _104718 f g p1 p2)). Qed.
Lemma lem4371380 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1894 _104717 _104718 f g p1 p2.
Proof. exact (EQ_MP (@lem4371379 _104717 _104718 f g p1 p2) (@lem4371301 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371420 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) (p1 : _104717) : (term1849 _104717 f t p1) = (term1849 _104717 f t p1).
Proof. exact (eq_refl (term1849 _104717 f t p1)). Qed.
Lemma lem4371421 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term1850 _104717 f p1) = (term1850 _104717 f p1).
Proof. exact (fun_ext (fun t : _104717 -> Prop => @lem4371420 _104717 f t p1)). Qed.
Lemma lem4371422 {_104717 : Type'} : (@all (_104717 -> Prop)) = (@all (_104717 -> Prop)).
Proof. exact (eq_refl (@all (_104717 -> Prop))). Qed.
Lemma lem4371424 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) : (term1851 _104717 f p1) = (term1851 _104717 f p1).
Proof. exact (MK_COMB (@lem4371422 _104717) (@lem4371421 _104717 f p1)). Qed.
Lemma lem4371425 {_104717 : Type'} (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1851 _104717 f p1.
Proof. exact (EQ_MP (@lem4371424 _104717 f p1) (@lem4371317 _104717 f p1 h1)). Qed.
Lemma lem4371449 {_104718 : Type'} (g : type686 _104718) (t : _104718 -> Prop) (p2 : _104718) : (term1849 _104718 g t p2) = (term1849 _104718 g t p2).
Proof. exact (eq_refl (term1849 _104718 g t p2)). Qed.
Lemma lem4371450 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term1850 _104718 g p2) = (term1850 _104718 g p2).
Proof. exact (fun_ext (fun t : _104718 -> Prop => @lem4371449 _104718 g t p2)). Qed.
Lemma lem4371451 {_104718 : Type'} : (@all (_104718 -> Prop)) = (@all (_104718 -> Prop)).
Proof. exact (eq_refl (@all (_104718 -> Prop))). Qed.
Lemma lem4371453 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) : (term1851 _104718 g p2) = (term1851 _104718 g p2).
Proof. exact (MK_COMB (@lem4371451 _104718) (@lem4371450 _104718 g p2)). Qed.
Lemma lem4371454 {_104718 : Type'} (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1851 _104718 g p2.
Proof. exact (EQ_MP (@lem4371453 _104718 g p2) (@lem4371318 _104718 g p2 h1)). Qed.
Lemma lem4371468 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t : _104758 -> Prop) (p2' : _104758) : (term1872 _104757 _104758 f' s p1' t p2') = (term1872 _104757 _104758 f' s p1' t p2').
Proof. exact (eq_refl (term1872 _104757 _104758 f' s p1' t p2')). Qed.
Lemma lem4371469 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1873 _104757 _104758 f' s p1' p2') = (term1873 _104757 _104758 f' s p1' p2').
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4371468 _104757 _104758 f' s p1' t p2')). Qed.
Lemma lem4371470 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4371472 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) : (term1874 _104757 _104758 f' s p1' p2') = (term1874 _104757 _104758 f' s p1' p2').
Proof. exact (MK_COMB (@lem4371470 _104758) (@lem4371469 _104757 _104758 f' s p1' p2')). Qed.
Lemma lem4371473 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1874 _104757 _104758 f' s p1' p2'.
Proof. exact (EQ_MP (@lem4371472 _104757 _104758 f' s p1' p2') (@lem4371323 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371501 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) (h1 : term1845 _104757 s p1') : term1845 _104757 s p1'.
Proof. exact (h1). Qed.
Lemma lem4371521 {_104758 : Type'} (f' : type686 _104758) (t : _104758 -> Prop) (p2' : _104758) : (term1849 _104758 f' t p2') = (term1849 _104758 f' t p2').
Proof. exact (eq_refl (term1849 _104758 f' t p2')). Qed.
Lemma lem4371522 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) : (term1850 _104758 f' p2') = (term1850 _104758 f' p2').
Proof. exact (fun_ext (fun t : _104758 -> Prop => @lem4371521 _104758 f' t p2')). Qed.
Lemma lem4371523 {_104758 : Type'} : (@all (_104758 -> Prop)) = (@all (_104758 -> Prop)).
Proof. exact (eq_refl (@all (_104758 -> Prop))). Qed.
Lemma lem4371525 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) : (term1851 _104758 f' p2') = (term1851 _104758 f' p2').
Proof. exact (MK_COMB (@lem4371523 _104758) (@lem4371522 _104758 f' p2')). Qed.
Lemma lem4371526 {_104758 : Type'} (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1851 _104758 f' p2'.
Proof. exact (EQ_MP (@lem4371525 _104758 f' p2') (@lem4371336 _104758 f' p2' h1)). Qed.
Lemma lem4371540 {_104795 _104796 : Type'} (f'' : type686 _104795) (s : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1858 _104795 _104796 f'' s p1'' t''' p2'') = (term1858 _104795 _104796 f'' s p1'' t''' p2'').
Proof. exact (eq_refl (term1858 _104795 _104796 f'' s p1'' t''' p2'')). Qed.
Lemma lem4371541 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1859 _104795 _104796 f'' p1'' t''' p2'') = (term1859 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (fun_ext (fun s : _104795 -> Prop => @lem4371540 _104795 _104796 f'' s p1'' t''' p2'')). Qed.
Lemma lem4371542 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4371544 {_104795 _104796 : Type'} (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1860 _104795 _104796 f'' p1'' t''' p2'') = (term1860 _104795 _104796 f'' p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4371542 _104795) (@lem4371541 _104795 _104796 f'' p1'' t''' p2'')). Qed.
Lemma lem4371545 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1860 _104795 _104796 f'' p1'' t''' p2''.
Proof. exact (EQ_MP (@lem4371544 _104795 _104796 f'' p1'' t''' p2'') (@lem4371339 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371577 {_104795 : Type'} (f'' : type686 _104795) (t : _104795 -> Prop) (p1'' : _104795) : (term1849 _104795 f'' t p1'') = (term1849 _104795 f'' t p1'').
Proof. exact (eq_refl (term1849 _104795 f'' t p1'')). Qed.
Lemma lem4371578 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) : (term1850 _104795 f'' p1'') = (term1850 _104795 f'' p1'').
Proof. exact (fun_ext (fun t : _104795 -> Prop => @lem4371577 _104795 f'' t p1'')). Qed.
Lemma lem4371579 {_104795 : Type'} : (@all (_104795 -> Prop)) = (@all (_104795 -> Prop)).
Proof. exact (eq_refl (@all (_104795 -> Prop))). Qed.
Lemma lem4371581 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) : (term1851 _104795 f'' p1'') = (term1851 _104795 f'' p1'').
Proof. exact (MK_COMB (@lem4371579 _104795) (@lem4371578 _104795 f'' p1'')). Qed.
Lemma lem4371582 {_104795 : Type'} (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1851 _104795 f'' p1''.
Proof. exact (EQ_MP (@lem4371581 _104795 f'' p1'') (@lem4371351 _104795 f'' p1'' h1)). Qed.
Lemma lem4371598 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') : term1845 _104796 t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371599 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1902 _104717 _104718 f g p1 p2 _49992.
Proof. exact (@lem4371380 _104717 _104718 t t' f g p1 p2 h1 _49992). Qed.
Lemma lem4371600 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (p2 : _104718) : (term1902 _104717 _104718 f g p1 p2 _49992) = (term1892 _104717 _104718 f g _49992 p1 p2).
Proof. exact (eq_refl (term1902 _104717 _104718 f g p1 p2 _49992)). Qed.
Lemma lem4371601 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1892 _104717 _104718 f g _49992 p1 p2.
Proof. exact (EQ_MP (@lem4371600 _104717 _104718 f g _49992 p1 p2) (@lem4371599 _104717 _104718 _49992 t t' f g p1 p2 h1)). Qed.
Lemma lem4371602 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (_49993 : _104718 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1903 _104717 _104718 f g _49992 p1 p2 _49993.
Proof. exact (@lem4371601 _104717 _104718 _49992 t t' f g p1 p2 h1 _49993). Qed.
Lemma lem4371603 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1903 _104717 _104718 f g _49992 p1 p2 _49993) = (term1890 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (eq_refl (term1903 _104717 _104718 f g _49992 p1 p2 _49993)). Qed.
Lemma lem4371604 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (_49993 : _104718 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1890 _104717 _104718 f g _49992 p1 _49993 p2.
Proof. exact (EQ_MP (@lem4371603 _104717 _104718 f g _49992 p1 _49993 p2) (@lem4371602 _104717 _104718 _49992 _49993 t t' f g p1 p2 h1)). Qed.
Lemma lem4371605 {_104717 : Type'} (_49994 : _104717 -> Prop) (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1904 _104717 f p1 _49994.
Proof. exact (@lem4371425 _104717 f p1 h1 _49994). Qed.
Lemma lem4371606 {_104717 : Type'} (f : type686 _104717) (_49994 : _104717 -> Prop) (p1 : _104717) : (term1904 _104717 f p1 _49994) = (term1849 _104717 f _49994 p1).
Proof. exact (eq_refl (term1904 _104717 f p1 _49994)). Qed.
Lemma lem4371608 {_104718 : Type'} (_49995 : _104718 -> Prop) (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1904 _104718 g p2 _49995.
Proof. exact (@lem4371454 _104718 g p2 h1 _49995). Qed.
Lemma lem4371609 {_104718 : Type'} (g : type686 _104718) (_49995 : _104718 -> Prop) (p2 : _104718) : (term1904 _104718 g p2 _49995) = (term1849 _104718 g _49995 p2).
Proof. exact (eq_refl (term1904 _104718 g p2 _49995)). Qed.
Lemma lem4371611 {_104757 _104758 : Type'} (_49996 : _104758 -> Prop) (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1905 _104757 _104758 f' s p1' p2' _49996.
Proof. exact (@lem4371473 _104757 _104758 t'' f' s p1' p2' h1 _49996). Qed.
Lemma lem4371612 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1905 _104757 _104758 f' s p1' p2' _49996) = (term1872 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (eq_refl (term1905 _104757 _104758 f' s p1' p2' _49996)). Qed.
Lemma lem4371614 {_104758 : Type'} (_49997 : _104758 -> Prop) (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1904 _104758 f' p2' _49997.
Proof. exact (@lem4371526 _104758 f' p2' h1 _49997). Qed.
Lemma lem4371615 {_104758 : Type'} (f' : type686 _104758) (_49997 : _104758 -> Prop) (p2' : _104758) : (term1904 _104758 f' p2' _49997) = (term1849 _104758 f' _49997 p2').
Proof. exact (eq_refl (term1904 _104758 f' p2' _49997)). Qed.
Lemma lem4371617 {_104795 _104796 : Type'} (_49998 : _104795 -> Prop) (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1906 _104795 _104796 f'' p1'' t''' p2'' _49998.
Proof. exact (@lem4371545 _104795 _104796 t'''' f'' p1'' t''' p2'' h1 _49998). Qed.
Lemma lem4371618 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1906 _104795 _104796 f'' p1'' t''' p2'' _49998) = (term1858 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (eq_refl (term1906 _104795 _104796 f'' p1'' t''' p2'' _49998)). Qed.
Lemma lem4371620 {_104795 : Type'} (_49999 : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1904 _104795 f'' p1'' _49999.
Proof. exact (@lem4371582 _104795 f'' p1'' h1 _49999). Qed.
Lemma lem4371621 {_104795 : Type'} (f'' : type686 _104795) (_49999 : _104795 -> Prop) (p1'' : _104795) : (term1904 _104795 f'' p1'' _49999) = (term1849 _104795 f'' _49999 p1'').
Proof. exact (eq_refl (term1904 _104795 f'' p1'' _49999)). Qed.
Lemma lem4371637 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1890 _104717 _104718 f g _49992 p1 _49993 p2) = (term1907 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (@lem4362904 (term1847 _104717 f _49992) (term1847 _104718 g _49993) (term1857 _104717 _104718 _49992 p1 _49993 p2)). Qed.
Lemma lem4371638 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (_49993 : _104718 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1907 _104717 _104718 f g _49992 p1 _49993 p2.
Proof. exact (EQ_MP (@lem4371637 _104717 _104718 f g _49992 p1 _49993 p2) (@lem4371604 _104717 _104718 _49992 _49993 t t' f g p1 p2 h1)). Qed.
Lemma lem4371660 {_104717 : Type'} (_49994 : _104717 -> Prop) (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1849 _104717 f _49994 p1.
Proof. exact (EQ_MP (@lem4371606 _104717 f _49994 p1) (@lem4371605 _104717 _49994 f p1 h1)). Qed.
Lemma lem4371674 {_104718 : Type'} (_49995 : _104718 -> Prop) (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1849 _104718 g _49995 p2.
Proof. exact (EQ_MP (@lem4371609 _104718 g _49995 p2) (@lem4371608 _104718 _49995 g p2 h1)). Qed.
Lemma lem4371684 {_104757 _104758 : Type'} (_49996 : _104758 -> Prop) (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1872 _104757 _104758 f' s p1' _49996 p2'.
Proof. exact (EQ_MP (@lem4371612 _104757 _104758 f' s p1' _49996 p2') (@lem4371611 _104757 _104758 _49996 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371698 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) (h1 : term1845 _104757 s p1') : term1845 _104757 s p1'.
Proof. exact (h1). Qed.
Lemma lem4371710 {_104758 : Type'} (_49997 : _104758 -> Prop) (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1849 _104758 f' _49997 p2'.
Proof. exact (EQ_MP (@lem4371615 _104758 f' _49997 p2') (@lem4371614 _104758 _49997 f' p2' h1)). Qed.
Lemma lem4371720 {_104795 _104796 : Type'} (_49998 : _104795 -> Prop) (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1858 _104795 _104796 f'' _49998 p1'' t''' p2''.
Proof. exact (EQ_MP (@lem4371618 _104795 _104796 f'' _49998 p1'' t''' p2'') (@lem4371617 _104795 _104796 _49998 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371738 {_104795 : Type'} (_49999 : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1849 _104795 f'' _49999 p1''.
Proof. exact (EQ_MP (@lem4371621 _104795 f'' _49999 p1'') (@lem4371620 _104795 _49999 f'' p1'' h1)). Qed.
Lemma lem4371746 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') : term1845 _104796 t''' p2''.
Proof. exact (h1). Qed.
Lemma lem4371748 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I ((_104717 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem4371304 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371749 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1908 _104717 f t.
Proof. exact (fun h0 : term1847 _104717 f t => @lem4371748 _104717 _104718 t t' f g p1 p2 h1). Qed.
Lemma lem4371751 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371752 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term1908 _104717 f t) = (@I ((_104717 -> Prop) -> Prop) f t).
Proof. exact (@lem4371751 (@I ((_104717 -> Prop) -> Prop) f t)). Qed.
Lemma lem4371753 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I ((_104717 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem4371752 _104717 f t) (@lem4371749 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371755 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I ((_104718 -> Prop) -> Prop) g t'.
Proof. exact (proj1 (@lem4371303 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371756 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1908 _104718 g t'.
Proof. exact (fun h0 : term1847 _104718 g t' => @lem4371755 _104717 _104718 t t' f g p1 p2 h1). Qed.
Lemma lem4371758 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371759 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) : (term1908 _104718 g t') = (@I ((_104718 -> Prop) -> Prop) g t').
Proof. exact (@lem4371758 (@I ((_104718 -> Prop) -> Prop) g t')). Qed.
Lemma lem4371760 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I ((_104718 -> Prop) -> Prop) g t'.
Proof. exact (EQ_MP (@lem4371759 _104718 g t') (@lem4371756 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371762 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I (_104717 -> Prop) t p1.
Proof. exact (proj2 (@lem4371304 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371763 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1910 _104717 t p1.
Proof. exact (fun h0 : term1845 _104717 t p1 => @lem4371762 _104717 _104718 t t' f g p1 p2 h1). Qed.
Lemma lem4371765 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371766 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (term1910 _104717 t p1) = (@I (_104717 -> Prop) t p1).
Proof. exact (@lem4371765 (@I (_104717 -> Prop) t p1)). Qed.
Lemma lem4371767 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I (_104717 -> Prop) t p1.
Proof. exact (EQ_MP (@lem4371766 _104717 t p1) (@lem4371763 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371769 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I (_104718 -> Prop) t' p2.
Proof. exact (proj2 (@lem4371303 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371770 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1910 _104718 t' p2.
Proof. exact (fun h0 : term1845 _104718 t' p2 => @lem4371769 _104717 _104718 t t' f g p1 p2 h1). Qed.
Lemma lem4371772 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371773 {_104718 : Type'} (t' : _104718 -> Prop) (p2 : _104718) : (term1910 _104718 t' p2) = (@I (_104718 -> Prop) t' p2).
Proof. exact (@lem4371772 (@I (_104718 -> Prop) t' p2)). Qed.
Lemma lem4371774 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : @I (_104718 -> Prop) t' p2.
Proof. exact (EQ_MP (@lem4371773 _104718 t' p2) (@lem4371770 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371776 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371777 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1857 _104717 _104718 _49992 p1 _49993 p2) = (term1913 _104717 _104718 _49992 p1 _49993 p2).
Proof. exact (@lem4371776 (@I (_104717 -> Prop) _49992 p1) (@I (_104718 -> Prop) _49993 p2)). Qed.
Lemma lem4371778 {_104718 : Type'} (g : type686 _104718) (_49993 : _104718 -> Prop) : (term1848 _104718 g _49993) = (term1848 _104718 g _49993).
Proof. exact (eq_refl (term1848 _104718 g _49993)). Qed.
Lemma lem4371779 {_104717 _104718 : Type'} (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1872 _104717 _104718 g _49992 p1 _49993 p2) = (term1914 _104717 _104718 g _49992 p1 _49993 p2).
Proof. exact (MK_COMB (@lem4371778 _104718 g _49993) (@lem4371777 _104717 _104718 _49992 p1 _49993 p2)). Qed.
Lemma lem4371781 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371782 {_104717 _104718 : Type'} (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1914 _104717 _104718 g _49992 p1 _49993 p2) = (term1915 _104717 _104718 g _49992 p1 _49993 p2).
Proof. exact (@lem4371781 (@I ((_104718 -> Prop) -> Prop) g _49993) (term1842 _104717 _104718 _49992 p1 _49993 p2)). Qed.
Lemma lem4371783 {_104717 _104718 : Type'} (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1872 _104717 _104718 g _49992 p1 _49993 p2) = (term1915 _104717 _104718 g _49992 p1 _49993 p2).
Proof. exact (TRANS (@lem4371779 _104717 _104718 g _49992 p1 _49993 p2) (@lem4371782 _104717 _104718 g _49992 p1 _49993 p2)). Qed.
Lemma lem4371784 {_104717 : Type'} (f : type686 _104717) (_49992 : _104717 -> Prop) : (term1848 _104717 f _49992) = (term1848 _104717 f _49992).
Proof. exact (eq_refl (term1848 _104717 f _49992)). Qed.
Lemma lem4371785 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1907 _104717 _104718 f g _49992 p1 _49993 p2) = (term1916 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (MK_COMB (@lem4371784 _104717 f _49992) (@lem4371783 _104717 _104718 g _49992 p1 _49993 p2)). Qed.
Lemma lem4371787 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371788 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1916 _104717 _104718 f g _49992 p1 _49993 p2) = (term1917 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (@lem4371787 (@I ((_104717 -> Prop) -> Prop) f _49992) (term1868 _104717 _104718 g _49992 p1 _49993 p2)). Qed.
Lemma lem4371789 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1907 _104717 _104718 f g _49992 p1 _49993 p2) = (term1917 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (TRANS (@lem4371785 _104717 _104718 f g _49992 p1 _49993 p2) (@lem4371788 _104717 _104718 f g _49992 p1 _49993 p2)). Qed.
Lemma lem4371791 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371792 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1917 _104717 _104718 f g _49992 p1 _49993 p2) = (term1918 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (@lem4371791 (term1919 _104717 _104718 f g _49992 p1 _49993 p2)). Qed.
Lemma lem4371793 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (_49992 : _104717 -> Prop) (p1 : _104717) (_49993 : _104718 -> Prop) (p2 : _104718) : (term1907 _104717 _104718 f g _49992 p1 _49993 p2) = (term1918 _104717 _104718 f g _49992 p1 _49993 p2).
Proof. exact (TRANS (@lem4371789 _104717 _104718 f g _49992 p1 _49993 p2) (@lem4371792 _104717 _104718 f g _49992 p1 _49993 p2)). Qed.
Lemma lem4371795 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1842 _104717 _104718 t p1 t' p2.
Proof. exact (conj (@lem4371767 _104717 _104718 t t' f g p1 p2 h1) (@lem4371774 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371796 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1868 _104717 _104718 g t p1 t' p2.
Proof. exact (conj (@lem4371760 _104717 _104718 t t' f g p1 p2 h1) (@lem4371795 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371797 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1919 _104717 _104718 f g t p1 t' p2.
Proof. exact (conj (@lem4371753 _104717 _104718 t t' f g p1 p2 h1) (@lem4371796 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371799 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (_49993 : _104718 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1918 _104717 _104718 f g _49992 p1 _49993 p2.
Proof. exact (EQ_MP (@lem4371793 _104717 _104718 f g _49992 p1 _49993 p2) (@lem4371638 _104717 _104718 _49992 _49993 t t' f g p1 p2 h1)). Qed.
Lemma lem4371800 {_104717 _104718 : Type'} (_49992 : _104717 -> Prop) (_49993 : _104718 -> Prop) (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1918 _104717 _104718 f g _49992 p1 _49993 p2.
Proof. exact (@lem4371799 _104717 _104718 _49992 _49993 t t' f g p1 p2 h1). Qed.
Lemma lem4371801 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1918 _104717 _104718 f g t p1 t' p2.
Proof. exact (@lem4371800 _104717 _104718 t t' t t' f g p1 p2 h1). Qed.
Lemma lem4371804 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : False.
Proof. exact (@lem4371801 _104717 _104718 t t' f g p1 p2 h1 (@lem4371797 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371805 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : term1920.
Proof. exact (fun h0 : ~ False => @lem4371804 _104717 _104718 t t' f g p1 p2 h1). Qed.
Lemma lem4371807 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371808 : term1920 = False.
Proof. exact (@lem4371807 False). Qed.
Lemma lem4371809 {_104717 _104718 : Type'} (t : _104717 -> Prop) (t' : _104718 -> Prop) (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1897 _104717 _104718 t t' f g p1 p2) : False.
Proof. exact (EQ_MP (@lem4371808) (@lem4371805 _104717 _104718 t t' f g p1 p2 h1)). Qed.
Lemma lem4371811 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I ((_104717 -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem4371312 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371812 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1908 _104717 f t.
Proof. exact (fun h0 : term1847 _104717 f t => @lem4371811 _104717 _104718 f g t p1 t' p2 h1). Qed.
Lemma lem4371814 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371815 {_104717 : Type'} (f : type686 _104717) (t : _104717 -> Prop) : (term1908 _104717 f t) = (@I ((_104717 -> Prop) -> Prop) f t).
Proof. exact (@lem4371814 (@I ((_104717 -> Prop) -> Prop) f t)). Qed.
Lemma lem4371816 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I ((_104717 -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem4371815 _104717 f t) (@lem4371812 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371818 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I (_104717 -> Prop) t p1.
Proof. exact (proj1 (@lem4371311 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371819 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1910 _104717 t p1.
Proof. exact (fun h0 : term1845 _104717 t p1 => @lem4371818 _104717 _104718 f g t p1 t' p2 h1). Qed.
Lemma lem4371821 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371822 {_104717 : Type'} (t : _104717 -> Prop) (p1 : _104717) : (term1910 _104717 t p1) = (@I (_104717 -> Prop) t p1).
Proof. exact (@lem4371821 (@I (_104717 -> Prop) t p1)). Qed.
Lemma lem4371823 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I (_104717 -> Prop) t p1.
Proof. exact (EQ_MP (@lem4371822 _104717 t p1) (@lem4371819 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371825 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371826 {_104717 : Type'} (f : type686 _104717) (_49994 : _104717 -> Prop) (p1 : _104717) : (term1849 _104717 f _49994 p1) = (term1921 _104717 f _49994 p1).
Proof. exact (@lem4371825 (@I ((_104717 -> Prop) -> Prop) f _49994) (@I (_104717 -> Prop) _49994 p1)). Qed.
Lemma lem4371828 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371829 {_104717 : Type'} (f : type686 _104717) (_49994 : _104717 -> Prop) (p1 : _104717) : (term1921 _104717 f _49994 p1) = (term1922 _104717 f _49994 p1).
Proof. exact (@lem4371828 (term1861 _104717 f _49994 p1)). Qed.
Lemma lem4371830 {_104717 : Type'} (f : type686 _104717) (_49994 : _104717 -> Prop) (p1 : _104717) : (term1849 _104717 f _49994 p1) = (term1922 _104717 f _49994 p1).
Proof. exact (TRANS (@lem4371826 _104717 f _49994 p1) (@lem4371829 _104717 f _49994 p1)). Qed.
Lemma lem4371832 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1861 _104717 f t p1.
Proof. exact (conj (@lem4371816 _104717 _104718 f g t p1 t' p2 h1) (@lem4371823 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371834 {_104717 : Type'} (_49994 : _104717 -> Prop) (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1922 _104717 f _49994 p1.
Proof. exact (EQ_MP (@lem4371830 _104717 f _49994 p1) (@lem4371660 _104717 _49994 f p1 h1)). Qed.
Lemma lem4371835 {_104717 : Type'} (_49994 : _104717 -> Prop) (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1922 _104717 f _49994 p1.
Proof. exact (@lem4371834 _104717 _49994 f p1 h1). Qed.
Lemma lem4371836 {_104717 : Type'} (t : _104717 -> Prop) (f : type686 _104717) (p1 : _104717) (h1 : term1851 _104717 f p1) : term1922 _104717 f t p1.
Proof. exact (@lem4371835 _104717 t f p1 h1). Qed.
Lemma lem4371839 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104717 f p1) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (@lem4371836 _104717 t f p1 h1 (@lem4371832 _104717 _104718 f g t p1 t' p2 h2)). Qed.
Lemma lem4371840 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104717 f p1) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : term1920.
Proof. exact (fun h0 : ~ False => @lem4371839 _104717 _104718 f g t p1 t' p2 h1 h2). Qed.
Lemma lem4371842 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371843 : term1920 = False.
Proof. exact (@lem4371842 False). Qed.
Lemma lem4371844 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104717 f p1) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (EQ_MP (@lem4371843) (@lem4371840 _104717 _104718 f g t p1 t' p2 h1 h2)). Qed.
Lemma lem4371846 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I ((_104718 -> Prop) -> Prop) g t'.
Proof. exact (proj2 (@lem4371312 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371847 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1908 _104718 g t'.
Proof. exact (fun h0 : term1847 _104718 g t' => @lem4371846 _104717 _104718 f g t p1 t' p2 h1). Qed.
Lemma lem4371849 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371850 {_104718 : Type'} (g : type686 _104718) (t' : _104718 -> Prop) : (term1908 _104718 g t') = (@I ((_104718 -> Prop) -> Prop) g t').
Proof. exact (@lem4371849 (@I ((_104718 -> Prop) -> Prop) g t')). Qed.
Lemma lem4371851 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I ((_104718 -> Prop) -> Prop) g t'.
Proof. exact (EQ_MP (@lem4371850 _104718 g t') (@lem4371847 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371853 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I (_104718 -> Prop) t' p2.
Proof. exact (proj2 (@lem4371311 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371854 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1910 _104718 t' p2.
Proof. exact (fun h0 : term1845 _104718 t' p2 => @lem4371853 _104717 _104718 f g t p1 t' p2 h1). Qed.
Lemma lem4371856 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371857 {_104718 : Type'} (t' : _104718 -> Prop) (p2 : _104718) : (term1910 _104718 t' p2) = (@I (_104718 -> Prop) t' p2).
Proof. exact (@lem4371856 (@I (_104718 -> Prop) t' p2)). Qed.
Lemma lem4371858 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : @I (_104718 -> Prop) t' p2.
Proof. exact (EQ_MP (@lem4371857 _104718 t' p2) (@lem4371854 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371860 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371861 {_104718 : Type'} (g : type686 _104718) (_49995 : _104718 -> Prop) (p2 : _104718) : (term1849 _104718 g _49995 p2) = (term1921 _104718 g _49995 p2).
Proof. exact (@lem4371860 (@I ((_104718 -> Prop) -> Prop) g _49995) (@I (_104718 -> Prop) _49995 p2)). Qed.
Lemma lem4371863 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371864 {_104718 : Type'} (g : type686 _104718) (_49995 : _104718 -> Prop) (p2 : _104718) : (term1921 _104718 g _49995 p2) = (term1922 _104718 g _49995 p2).
Proof. exact (@lem4371863 (term1861 _104718 g _49995 p2)). Qed.
Lemma lem4371865 {_104718 : Type'} (g : type686 _104718) (_49995 : _104718 -> Prop) (p2 : _104718) : (term1849 _104718 g _49995 p2) = (term1922 _104718 g _49995 p2).
Proof. exact (TRANS (@lem4371861 _104718 g _49995 p2) (@lem4371864 _104718 g _49995 p2)). Qed.
Lemma lem4371867 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : term1861 _104718 g t' p2.
Proof. exact (conj (@lem4371851 _104717 _104718 f g t p1 t' p2 h1) (@lem4371858 _104717 _104718 f g t p1 t' p2 h1)). Qed.
Lemma lem4371869 {_104718 : Type'} (_49995 : _104718 -> Prop) (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1922 _104718 g _49995 p2.
Proof. exact (EQ_MP (@lem4371865 _104718 g _49995 p2) (@lem4371674 _104718 _49995 g p2 h1)). Qed.
Lemma lem4371870 {_104718 : Type'} (_49995 : _104718 -> Prop) (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1922 _104718 g _49995 p2.
Proof. exact (@lem4371869 _104718 _49995 g p2 h1). Qed.
Lemma lem4371871 {_104718 : Type'} (t' : _104718 -> Prop) (g : type686 _104718) (p2 : _104718) (h1 : term1851 _104718 g p2) : term1922 _104718 g t' p2.
Proof. exact (@lem4371870 _104718 t' g p2 h1). Qed.
Lemma lem4371874 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104718 g p2) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (@lem4371871 _104718 t' g p2 h1 (@lem4371867 _104717 _104718 f g t p1 t' p2 h2)). Qed.
Lemma lem4371875 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104718 g p2) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : term1920.
Proof. exact (fun h0 : ~ False => @lem4371874 _104717 _104718 f g t p1 t' p2 h1 h2). Qed.
Lemma lem4371877 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371878 : term1920 = False.
Proof. exact (@lem4371877 False). Qed.
Lemma lem4371879 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104718 g p2) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (EQ_MP (@lem4371878) (@lem4371875 _104717 _104718 f g t p1 t' p2 h1 h2)). Qed.
Lemma lem4371881 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I ((_104758 -> Prop) -> Prop) f' t''.
Proof. exact (proj1 (@lem4371325 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371882 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1908 _104758 f' t''.
Proof. exact (fun h0 : term1847 _104758 f' t'' => @lem4371881 _104757 _104758 t'' f' s p1' p2' h1). Qed.
Lemma lem4371884 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371885 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (term1908 _104758 f' t'') = (@I ((_104758 -> Prop) -> Prop) f' t'').
Proof. exact (@lem4371884 (@I ((_104758 -> Prop) -> Prop) f' t'')). Qed.
Lemma lem4371886 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I ((_104758 -> Prop) -> Prop) f' t''.
Proof. exact (EQ_MP (@lem4371885 _104758 f' t'') (@lem4371882 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371888 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I (_104757 -> Prop) s p1'.
Proof. exact (proj1 (@lem4371324 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371889 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1910 _104757 s p1'.
Proof. exact (fun h0 : term1845 _104757 s p1' => @lem4371888 _104757 _104758 t'' f' s p1' p2' h1). Qed.
Lemma lem4371891 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371892 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term1910 _104757 s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4371891 (@I (_104757 -> Prop) s p1')). Qed.
Lemma lem4371893 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I (_104757 -> Prop) s p1'.
Proof. exact (EQ_MP (@lem4371892 _104757 s p1') (@lem4371889 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371895 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I (_104758 -> Prop) t'' p2'.
Proof. exact (proj2 (@lem4371325 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371896 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1910 _104758 t'' p2'.
Proof. exact (fun h0 : term1845 _104758 t'' p2' => @lem4371895 _104757 _104758 t'' f' s p1' p2' h1). Qed.
Lemma lem4371898 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371899 {_104758 : Type'} (t'' : _104758 -> Prop) (p2' : _104758) : (term1910 _104758 t'' p2') = (@I (_104758 -> Prop) t'' p2').
Proof. exact (@lem4371898 (@I (_104758 -> Prop) t'' p2')). Qed.
Lemma lem4371900 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : @I (_104758 -> Prop) t'' p2'.
Proof. exact (EQ_MP (@lem4371899 _104758 t'' p2') (@lem4371896 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371902 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371903 {_104757 _104758 : Type'} (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1857 _104757 _104758 s p1' _49996 p2') = (term1913 _104757 _104758 s p1' _49996 p2').
Proof. exact (@lem4371902 (@I (_104757 -> Prop) s p1') (@I (_104758 -> Prop) _49996 p2')). Qed.
Lemma lem4371904 {_104758 : Type'} (f' : type686 _104758) (_49996 : _104758 -> Prop) : (term1848 _104758 f' _49996) = (term1848 _104758 f' _49996).
Proof. exact (eq_refl (term1848 _104758 f' _49996)). Qed.
Lemma lem4371905 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1872 _104757 _104758 f' s p1' _49996 p2') = (term1914 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (MK_COMB (@lem4371904 _104758 f' _49996) (@lem4371903 _104757 _104758 s p1' _49996 p2')). Qed.
Lemma lem4371907 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371908 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1914 _104757 _104758 f' s p1' _49996 p2') = (term1915 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (@lem4371907 (@I ((_104758 -> Prop) -> Prop) f' _49996) (term1842 _104757 _104758 s p1' _49996 p2')). Qed.
Lemma lem4371909 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1872 _104757 _104758 f' s p1' _49996 p2') = (term1915 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (TRANS (@lem4371905 _104757 _104758 f' s p1' _49996 p2') (@lem4371908 _104757 _104758 f' s p1' _49996 p2')). Qed.
Lemma lem4371911 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371912 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1915 _104757 _104758 f' s p1' _49996 p2') = (term1923 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (@lem4371911 (term1868 _104757 _104758 f' s p1' _49996 p2')). Qed.
Lemma lem4371913 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (_49996 : _104758 -> Prop) (p2' : _104758) : (term1872 _104757 _104758 f' s p1' _49996 p2') = (term1923 _104757 _104758 f' s p1' _49996 p2').
Proof. exact (TRANS (@lem4371909 _104757 _104758 f' s p1' _49996 p2') (@lem4371912 _104757 _104758 f' s p1' _49996 p2')). Qed.
Lemma lem4371915 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1842 _104757 _104758 s p1' t'' p2'.
Proof. exact (conj (@lem4371893 _104757 _104758 t'' f' s p1' p2' h1) (@lem4371900 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371916 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1868 _104757 _104758 f' s p1' t'' p2'.
Proof. exact (conj (@lem4371886 _104757 _104758 t'' f' s p1' p2' h1) (@lem4371915 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371918 {_104757 _104758 : Type'} (_49996 : _104758 -> Prop) (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1923 _104757 _104758 f' s p1' _49996 p2'.
Proof. exact (EQ_MP (@lem4371913 _104757 _104758 f' s p1' _49996 p2') (@lem4371684 _104757 _104758 _49996 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371919 {_104757 _104758 : Type'} (_49996 : _104758 -> Prop) (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1923 _104757 _104758 f' s p1' _49996 p2'.
Proof. exact (@lem4371918 _104757 _104758 _49996 t'' f' s p1' p2' h1). Qed.
Lemma lem4371920 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1923 _104757 _104758 f' s p1' t'' p2'.
Proof. exact (@lem4371919 _104757 _104758 t'' t'' f' s p1' p2' h1). Qed.
Lemma lem4371923 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : False.
Proof. exact (@lem4371920 _104757 _104758 t'' f' s p1' p2' h1 (@lem4371916 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371924 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : term1920.
Proof. exact (fun h0 : ~ False => @lem4371923 _104757 _104758 t'' f' s p1' p2' h1). Qed.
Lemma lem4371926 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371927 : term1920 = False.
Proof. exact (@lem4371926 False). Qed.
Lemma lem4371928 {_104757 _104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1877 _104757 _104758 t'' f' s p1' p2') : False.
Proof. exact (EQ_MP (@lem4371927) (@lem4371924 _104757 _104758 t'' f' s p1' p2' h1)). Qed.
Lemma lem4371930 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I (_104757 -> Prop) s p1'.
Proof. exact (proj1 (@lem4371331 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371931 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1910 _104757 s p1'.
Proof. exact (fun h0 : term1845 _104757 s p1' => @lem4371930 _104757 _104758 f' s p1' t'' p2' h1). Qed.
Lemma lem4371933 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371934 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term1910 _104757 s p1') = (@I (_104757 -> Prop) s p1').
Proof. exact (@lem4371933 (@I (_104757 -> Prop) s p1')). Qed.
Lemma lem4371935 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I (_104757 -> Prop) s p1'.
Proof. exact (EQ_MP (@lem4371934 _104757 s p1') (@lem4371931 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371938 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371940 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) : (term1845 _104757 s p1') = (term1924 _104757 s p1').
Proof. exact (@lem4371938 (@I (_104757 -> Prop) s p1')). Qed.
Lemma lem4371943 {_104757 : Type'} (s : _104757 -> Prop) (p1' : _104757) (h1 : term1845 _104757 s p1') : term1924 _104757 s p1'.
Proof. exact (EQ_MP (@lem4371940 _104757 s p1') (@lem4371698 _104757 s p1' h1)). Qed.
Lemma lem4371946 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (@lem4371943 _104757 s p1' h1 (@lem4371935 _104757 _104758 f' s p1' t'' p2' h2)). Qed.
Lemma lem4371947 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : term1920.
Proof. exact (fun h0 : ~ False => @lem4371946 _104757 _104758 f' s p1' t'' p2' h1 h2). Qed.
Lemma lem4371949 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371950 : term1920 = False.
Proof. exact (@lem4371949 False). Qed.
Lemma lem4371951 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4371950) (@lem4371947 _104757 _104758 f' s p1' t'' p2' h1 h2)). Qed.
Lemma lem4371953 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I ((_104758 -> Prop) -> Prop) f' t''.
Proof. exact (proj1 (@lem4371329 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371954 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1908 _104758 f' t''.
Proof. exact (fun h0 : term1847 _104758 f' t'' => @lem4371953 _104757 _104758 f' s p1' t'' p2' h1). Qed.
Lemma lem4371956 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371957 {_104758 : Type'} (f' : type686 _104758) (t'' : _104758 -> Prop) : (term1908 _104758 f' t'') = (@I ((_104758 -> Prop) -> Prop) f' t'').
Proof. exact (@lem4371956 (@I ((_104758 -> Prop) -> Prop) f' t'')). Qed.
Lemma lem4371958 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I ((_104758 -> Prop) -> Prop) f' t''.
Proof. exact (EQ_MP (@lem4371957 _104758 f' t'') (@lem4371954 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371960 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I (_104758 -> Prop) t'' p2'.
Proof. exact (proj2 (@lem4371331 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371961 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1910 _104758 t'' p2'.
Proof. exact (fun h0 : term1845 _104758 t'' p2' => @lem4371960 _104757 _104758 f' s p1' t'' p2' h1). Qed.
Lemma lem4371963 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371964 {_104758 : Type'} (t'' : _104758 -> Prop) (p2' : _104758) : (term1910 _104758 t'' p2') = (@I (_104758 -> Prop) t'' p2').
Proof. exact (@lem4371963 (@I (_104758 -> Prop) t'' p2')). Qed.
Lemma lem4371965 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : @I (_104758 -> Prop) t'' p2'.
Proof. exact (EQ_MP (@lem4371964 _104758 t'' p2') (@lem4371961 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371967 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4371968 {_104758 : Type'} (f' : type686 _104758) (_49997 : _104758 -> Prop) (p2' : _104758) : (term1849 _104758 f' _49997 p2') = (term1921 _104758 f' _49997 p2').
Proof. exact (@lem4371967 (@I ((_104758 -> Prop) -> Prop) f' _49997) (@I (_104758 -> Prop) _49997 p2')). Qed.
Lemma lem4371970 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4371971 {_104758 : Type'} (f' : type686 _104758) (_49997 : _104758 -> Prop) (p2' : _104758) : (term1921 _104758 f' _49997 p2') = (term1922 _104758 f' _49997 p2').
Proof. exact (@lem4371970 (term1861 _104758 f' _49997 p2')). Qed.
Lemma lem4371972 {_104758 : Type'} (f' : type686 _104758) (_49997 : _104758 -> Prop) (p2' : _104758) : (term1849 _104758 f' _49997 p2') = (term1922 _104758 f' _49997 p2').
Proof. exact (TRANS (@lem4371968 _104758 f' _49997 p2') (@lem4371971 _104758 f' _49997 p2')). Qed.
Lemma lem4371974 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : term1861 _104758 f' t'' p2'.
Proof. exact (conj (@lem4371958 _104757 _104758 f' s p1' t'' p2' h1) (@lem4371965 _104757 _104758 f' s p1' t'' p2' h1)). Qed.
Lemma lem4371976 {_104758 : Type'} (_49997 : _104758 -> Prop) (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1922 _104758 f' _49997 p2'.
Proof. exact (EQ_MP (@lem4371972 _104758 f' _49997 p2') (@lem4371710 _104758 _49997 f' p2' h1)). Qed.
Lemma lem4371977 {_104758 : Type'} (_49997 : _104758 -> Prop) (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1922 _104758 f' _49997 p2'.
Proof. exact (@lem4371976 _104758 _49997 f' p2' h1). Qed.
Lemma lem4371978 {_104758 : Type'} (t'' : _104758 -> Prop) (f' : type686 _104758) (p2' : _104758) (h1 : term1851 _104758 f' p2') : term1922 _104758 f' t'' p2'.
Proof. exact (@lem4371977 _104758 t'' f' p2' h1). Qed.
Lemma lem4371981 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1851 _104758 f' p2') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (@lem4371978 _104758 t'' f' p2' h1 (@lem4371974 _104757 _104758 f' s p1' t'' p2' h2)). Qed.
Lemma lem4371982 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1851 _104758 f' p2') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : term1920.
Proof. exact (fun h0 : ~ False => @lem4371981 _104757 _104758 f' s p1' t'' p2' h1 h2). Qed.
Lemma lem4371984 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371985 : term1920 = False.
Proof. exact (@lem4371984 False). Qed.
Lemma lem4371986 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1851 _104758 f' p2') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4371985) (@lem4371982 _104757 _104758 f' s p1' t'' p2' h1 h2)). Qed.
Lemma lem4371988 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I ((_104795 -> Prop) -> Prop) f'' t''''.
Proof. exact (proj1 (@lem4371342 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371989 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1908 _104795 f'' t''''.
Proof. exact (fun h0 : term1847 _104795 f'' t'''' => @lem4371988 _104795 _104796 t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4371991 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371992 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (term1908 _104795 f'' t'''') = (@I ((_104795 -> Prop) -> Prop) f'' t'''').
Proof. exact (@lem4371991 (@I ((_104795 -> Prop) -> Prop) f'' t'''')). Qed.
Lemma lem4371993 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I ((_104795 -> Prop) -> Prop) f'' t''''.
Proof. exact (EQ_MP (@lem4371992 _104795 f'' t'''') (@lem4371989 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371995 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I (_104795 -> Prop) t'''' p1''.
Proof. exact (proj2 (@lem4371342 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4371996 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1910 _104795 t'''' p1''.
Proof. exact (fun h0 : term1845 _104795 t'''' p1'' => @lem4371995 _104795 _104796 t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4371998 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4371999 {_104795 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) : (term1910 _104795 t'''' p1'') = (@I (_104795 -> Prop) t'''' p1'').
Proof. exact (@lem4371998 (@I (_104795 -> Prop) t'''' p1'')). Qed.
Lemma lem4372000 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I (_104795 -> Prop) t'''' p1''.
Proof. exact (EQ_MP (@lem4371999 _104795 t'''' p1'') (@lem4371996 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372002 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I (_104796 -> Prop) t''' p2''.
Proof. exact (proj2 (@lem4371340 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372003 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1910 _104796 t''' p2''.
Proof. exact (fun h0 : term1845 _104796 t''' p2'' => @lem4372002 _104795 _104796 t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4372005 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372006 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (term1910 _104796 t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4372005 (@I (_104796 -> Prop) t''' p2'')). Qed.
Lemma lem4372007 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : @I (_104796 -> Prop) t''' p2''.
Proof. exact (EQ_MP (@lem4372006 _104796 t''' p2'') (@lem4372003 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372009 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4372010 {_104795 _104796 : Type'} (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1857 _104795 _104796 _49998 p1'' t''' p2'') = (term1913 _104795 _104796 _49998 p1'' t''' p2'').
Proof. exact (@lem4372009 (@I (_104795 -> Prop) _49998 p1'') (@I (_104796 -> Prop) t''' p2'')). Qed.
Lemma lem4372011 {_104795 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) : (term1848 _104795 f'' _49998) = (term1848 _104795 f'' _49998).
Proof. exact (eq_refl (term1848 _104795 f'' _49998)). Qed.
Lemma lem4372012 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1858 _104795 _104796 f'' _49998 p1'' t''' p2'') = (term1925 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (MK_COMB (@lem4372011 _104795 f'' _49998) (@lem4372010 _104795 _104796 _49998 p1'' t''' p2'')). Qed.
Lemma lem4372014 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4372015 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1925 _104795 _104796 f'' _49998 p1'' t''' p2'') = (term1926 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (@lem4372014 (@I ((_104795 -> Prop) -> Prop) f'' _49998) (term1842 _104795 _104796 _49998 p1'' t''' p2'')). Qed.
Lemma lem4372016 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1858 _104795 _104796 f'' _49998 p1'' t''' p2'') = (term1926 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (TRANS (@lem4372012 _104795 _104796 f'' _49998 p1'' t''' p2'') (@lem4372015 _104795 _104796 f'' _49998 p1'' t''' p2'')). Qed.
Lemma lem4372018 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4372019 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1926 _104795 _104796 f'' _49998 p1'' t''' p2'') = (term1927 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (@lem4372018 (term1844 _104795 _104796 f'' _49998 p1'' t''' p2'')). Qed.
Lemma lem4372020 {_104795 _104796 : Type'} (f'' : type686 _104795) (_49998 : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) : (term1858 _104795 _104796 f'' _49998 p1'' t''' p2'') = (term1927 _104795 _104796 f'' _49998 p1'' t''' p2'').
Proof. exact (TRANS (@lem4372016 _104795 _104796 f'' _49998 p1'' t''' p2'') (@lem4372019 _104795 _104796 f'' _49998 p1'' t''' p2'')). Qed.
Lemma lem4372022 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1842 _104795 _104796 t'''' p1'' t''' p2''.
Proof. exact (conj (@lem4372000 _104795 _104796 t'''' f'' p1'' t''' p2'' h1) (@lem4372007 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372023 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1844 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (conj (@lem4371993 _104795 _104796 t'''' f'' p1'' t''' p2'' h1) (@lem4372022 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372025 {_104795 _104796 : Type'} (_49998 : _104795 -> Prop) (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1927 _104795 _104796 f'' _49998 p1'' t''' p2''.
Proof. exact (EQ_MP (@lem4372020 _104795 _104796 f'' _49998 p1'' t''' p2'') (@lem4371720 _104795 _104796 _49998 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372026 {_104795 _104796 : Type'} (_49998 : _104795 -> Prop) (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1927 _104795 _104796 f'' _49998 p1'' t''' p2''.
Proof. exact (@lem4372025 _104795 _104796 _49998 t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4372027 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1927 _104795 _104796 f'' t'''' p1'' t''' p2''.
Proof. exact (@lem4372026 _104795 _104796 t'''' t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4372030 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : False.
Proof. exact (@lem4372027 _104795 _104796 t'''' f'' p1'' t''' p2'' h1 (@lem4372023 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372031 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : term1920.
Proof. exact (fun h0 : ~ False => @lem4372030 _104795 _104796 t'''' f'' p1'' t''' p2'' h1). Qed.
Lemma lem4372033 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372034 : term1920 = False.
Proof. exact (@lem4372033 False). Qed.
Lemma lem4372035 {_104795 _104796 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372034) (@lem4372031 _104795 _104796 t'''' f'' p1'' t''' p2'' h1)). Qed.
Lemma lem4372037 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I ((_104795 -> Prop) -> Prop) f'' t''''.
Proof. exact (proj1 (@lem4371345 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372038 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1908 _104795 f'' t''''.
Proof. exact (fun h0 : term1847 _104795 f'' t'''' => @lem4372037 _104795 _104796 f'' t'''' p1'' t''' p2'' h1). Qed.
Lemma lem4372040 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372041 {_104795 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) : (term1908 _104795 f'' t'''') = (@I ((_104795 -> Prop) -> Prop) f'' t'''').
Proof. exact (@lem4372040 (@I ((_104795 -> Prop) -> Prop) f'' t'''')). Qed.
Lemma lem4372042 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I ((_104795 -> Prop) -> Prop) f'' t''''.
Proof. exact (EQ_MP (@lem4372041 _104795 f'' t'''') (@lem4372038 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372044 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I (_104795 -> Prop) t'''' p1''.
Proof. exact (proj1 (@lem4371347 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372045 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1910 _104795 t'''' p1''.
Proof. exact (fun h0 : term1845 _104795 t'''' p1'' => @lem4372044 _104795 _104796 f'' t'''' p1'' t''' p2'' h1). Qed.
Lemma lem4372047 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372048 {_104795 : Type'} (t'''' : _104795 -> Prop) (p1'' : _104795) : (term1910 _104795 t'''' p1'') = (@I (_104795 -> Prop) t'''' p1'').
Proof. exact (@lem4372047 (@I (_104795 -> Prop) t'''' p1'')). Qed.
Lemma lem4372049 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I (_104795 -> Prop) t'''' p1''.
Proof. exact (EQ_MP (@lem4372048 _104795 t'''' p1'') (@lem4372045 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372051 (a : Prop) (b : Prop) : (term1911 a b) = (term1912 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4372052 {_104795 : Type'} (f'' : type686 _104795) (_49999 : _104795 -> Prop) (p1'' : _104795) : (term1849 _104795 f'' _49999 p1'') = (term1921 _104795 f'' _49999 p1'').
Proof. exact (@lem4372051 (@I ((_104795 -> Prop) -> Prop) f'' _49999) (@I (_104795 -> Prop) _49999 p1'')). Qed.
Lemma lem4372054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4372055 {_104795 : Type'} (f'' : type686 _104795) (_49999 : _104795 -> Prop) (p1'' : _104795) : (term1921 _104795 f'' _49999 p1'') = (term1922 _104795 f'' _49999 p1'').
Proof. exact (@lem4372054 (term1861 _104795 f'' _49999 p1'')). Qed.
Lemma lem4372056 {_104795 : Type'} (f'' : type686 _104795) (_49999 : _104795 -> Prop) (p1'' : _104795) : (term1849 _104795 f'' _49999 p1'') = (term1922 _104795 f'' _49999 p1'').
Proof. exact (TRANS (@lem4372052 _104795 f'' _49999 p1'') (@lem4372055 _104795 f'' _49999 p1'')). Qed.
Lemma lem4372058 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1861 _104795 f'' t'''' p1''.
Proof. exact (conj (@lem4372042 _104795 _104796 f'' t'''' p1'' t''' p2'' h1) (@lem4372049 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372060 {_104795 : Type'} (_49999 : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1922 _104795 f'' _49999 p1''.
Proof. exact (EQ_MP (@lem4372056 _104795 f'' _49999 p1'') (@lem4371738 _104795 _49999 f'' p1'' h1)). Qed.
Lemma lem4372061 {_104795 : Type'} (_49999 : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1922 _104795 f'' _49999 p1''.
Proof. exact (@lem4372060 _104795 _49999 f'' p1'' h1). Qed.
Lemma lem4372062 {_104795 : Type'} (t'''' : _104795 -> Prop) (f'' : type686 _104795) (p1'' : _104795) (h1 : term1851 _104795 f'' p1'') : term1922 _104795 f'' t'''' p1''.
Proof. exact (@lem4372061 _104795 t'''' f'' p1'' h1). Qed.
Lemma lem4372065 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1851 _104795 f'' p1'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (@lem4372062 _104795 t'''' f'' p1'' h1 (@lem4372058 _104795 _104796 f'' t'''' p1'' t''' p2'' h2)). Qed.
Lemma lem4372066 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1851 _104795 f'' p1'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1920.
Proof. exact (fun h0 : ~ False => @lem4372065 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2). Qed.
Lemma lem4372068 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372069 : term1920 = False.
Proof. exact (@lem4372068 False). Qed.
Lemma lem4372070 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1851 _104795 f'' p1'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372069) (@lem4372066 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2)). Qed.
Lemma lem4372072 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I (_104796 -> Prop) t''' p2''.
Proof. exact (proj2 (@lem4371347 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372073 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1910 _104796 t''' p2''.
Proof. exact (fun h0 : term1845 _104796 t''' p2'' => @lem4372072 _104795 _104796 f'' t'''' p1'' t''' p2'' h1). Qed.
Lemma lem4372075 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372076 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (term1910 _104796 t''' p2'') = (@I (_104796 -> Prop) t''' p2'').
Proof. exact (@lem4372075 (@I (_104796 -> Prop) t''' p2'')). Qed.
Lemma lem4372077 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : @I (_104796 -> Prop) t''' p2''.
Proof. exact (EQ_MP (@lem4372076 _104796 t''' p2'') (@lem4372073 _104795 _104796 f'' t'''' p1'' t''' p2'' h1)). Qed.
Lemma lem4372080 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4372082 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) : (term1845 _104796 t''' p2'') = (term1924 _104796 t''' p2'').
Proof. exact (@lem4372080 (@I (_104796 -> Prop) t''' p2'')). Qed.
Lemma lem4372085 {_104796 : Type'} (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') : term1924 _104796 t''' p2''.
Proof. exact (EQ_MP (@lem4372082 _104796 t''' p2'') (@lem4371746 _104796 t''' p2'' h1)). Qed.
Lemma lem4372088 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (@lem4372085 _104796 t''' p2'' h1 (@lem4372077 _104795 _104796 f'' t'''' p1'' t''' p2'' h2)). Qed.
Lemma lem4372089 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : term1920.
Proof. exact (fun h0 : ~ False => @lem4372088 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2). Qed.
Lemma lem4372091 (p : Prop) : (term1909 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4372092 : term1920 = False.
Proof. exact (@lem4372091 False). Qed.
Lemma lem4372093 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372092) (@lem4372089 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2)). Qed.
Lemma lem4372094 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : (term1845 _104796 t''' p2'') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104796 t''' p2'' => @lem4372093 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (fun h3 : False => @lem4371746 _104796 t''' p2'' h1)). Qed.
Lemma lem4372095 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372094 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (@lem4371746 _104796 t''' p2'' h1)). Qed.
Lemma lem4372096 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : (term1845 _104757 s p1') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104757 s p1' => @lem4371951 _104757 _104758 f' s p1' t'' p2' h1 h2) (fun h3 : False => @lem4371698 _104757 s p1' h1)). Qed.
Lemma lem4372097 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4372096 _104757 _104758 f' s p1' t'' p2' h1 h2) (@lem4371698 _104757 s p1' h1)). Qed.
Lemma lem4372098 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : (term1845 _104796 t''' p2'') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104796 t''' p2'' => @lem4372095 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (fun h3 : False => @lem4371598 _104796 t''' p2'' h1)). Qed.
Lemma lem4372099 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372098 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (@lem4371598 _104796 t''' p2'' h1)). Qed.
Lemma lem4372100 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : (term1845 _104757 s p1') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104757 s p1' => @lem4372097 _104757 _104758 f' s p1' t'' p2' h1 h2) (fun h3 : False => @lem4371501 _104757 s p1' h1)). Qed.
Lemma lem4372101 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4372100 _104757 _104758 f' s p1' t'' p2' h1 h2) (@lem4371501 _104757 s p1' h1)). Qed.
Lemma lem4372102 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : (term1845 _104796 t''' p2'') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104796 t''' p2'' => @lem4372099 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (fun h3 : False => @lem4371598 _104796 t''' p2'' h1)). Qed.
Lemma lem4372103 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1845 _104796 t''' p2'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372102 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (@lem4371598 _104796 t''' p2'' h1)). Qed.
Lemma lem4372104 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1851 _104795 f'' p1'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : (term1851 _104795 f'' p1'') = False.
Proof. exact (prop_ext (fun h3 : term1851 _104795 f'' p1'' => @lem4372070 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (fun h3 : False => @lem4371582 _104795 f'' p1'' h1)). Qed.
Lemma lem4372105 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1851 _104795 f'' p1'') (h2 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (EQ_MP (@lem4372104 _104795 _104796 f'' t'''' p1'' t''' p2'' h1 h2) (@lem4371582 _104795 f'' p1'' h1)). Qed.
Lemma lem4372106 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1851 _104758 f' p2') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : (term1851 _104758 f' p2') = False.
Proof. exact (prop_ext (fun h3 : term1851 _104758 f' p2' => @lem4371986 _104757 _104758 f' s p1' t'' p2' h1 h2) (fun h3 : False => @lem4371526 _104758 f' p2' h1)). Qed.
Lemma lem4372107 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1851 _104758 f' p2') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4372106 _104757 _104758 f' s p1' t'' p2' h1 h2) (@lem4371526 _104758 f' p2' h1)). Qed.
Lemma lem4372108 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : (term1845 _104757 s p1') = False.
Proof. exact (prop_ext (fun h3 : term1845 _104757 s p1' => @lem4372101 _104757 _104758 f' s p1' t'' p2' h1 h2) (fun h3 : False => @lem4371501 _104757 s p1' h1)). Qed.
Lemma lem4372109 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1845 _104757 s p1') (h2 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (EQ_MP (@lem4372108 _104757 _104758 f' s p1' t'' p2' h1 h2) (@lem4371501 _104757 s p1' h1)). Qed.
Lemma lem4372110 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104718 g p2) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : (term1851 _104718 g p2) = False.
Proof. exact (prop_ext (fun h3 : term1851 _104718 g p2 => @lem4371879 _104717 _104718 f g t p1 t' p2 h1 h2) (fun h3 : False => @lem4371454 _104718 g p2 h1)). Qed.
Lemma lem4372111 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104718 g p2) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (EQ_MP (@lem4372110 _104717 _104718 f g t p1 t' p2 h1 h2) (@lem4371454 _104718 g p2 h1)). Qed.
Lemma lem4372112 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104717 f p1) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : (term1851 _104717 f p1) = False.
Proof. exact (prop_ext (fun h3 : term1851 _104717 f p1 => @lem4371844 _104717 _104718 f g t p1 t' p2 h1 h2) (fun h3 : False => @lem4371425 _104717 f p1 h1)). Qed.
Lemma lem4372113 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1851 _104717 f p1) (h2 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (EQ_MP (@lem4372112 _104717 _104718 f g t p1 t' p2 h1 h2) (@lem4371425 _104717 f p1 h1)). Qed.
Lemma lem4372114 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (or_elim (@lem4371346 _104795 _104796 f'' t'''' p1'' t''' p2'' h1) (fun h0 : term1851 _104795 f'' p1'' => @lem4372105 _104795 _104796 f'' t'''' p1'' t''' p2'' h0 h1) (fun h0 : term1845 _104796 t''' p2'' => @lem4372103 _104795 _104796 f'' t'''' p1'' t''' p2'' h0 h1)). Qed.
Lemma lem4372115 {_104795 _104796 : Type'} (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1867 _104795 _104796 f'' t'''' p1'' t''' p2'') : False.
Proof. exact (or_elim (@lem4371320 _104795 _104796 f'' t'''' p1'' t''' p2'' h1) (fun h0 : term1865 _104795 _104796 t'''' f'' p1'' t''' p2'' => @lem4372035 _104795 _104796 t'''' f'' p1'' t''' p2'' h0) (fun h0 : term1855 _104795 _104796 f'' t'''' p1'' t''' p2'' => @lem4372114 _104795 _104796 f'' t'''' p1'' t''' p2'' h0)). Qed.
Lemma lem4372116 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1871 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (or_elim (@lem4371330 _104757 _104758 f' s p1' t'' p2' h1) (fun h0 : term1845 _104757 s p1' => @lem4372109 _104757 _104758 f' s p1' t'' p2' h0 h1) (fun h0 : term1851 _104758 f' p2' => @lem4372107 _104757 _104758 f' s p1' t'' p2' h0 h1)). Qed.
Lemma lem4372117 {_104757 _104758 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1879 _104757 _104758 f' s p1' t'' p2') : False.
Proof. exact (or_elim (@lem4371319 _104757 _104758 f' s p1' t'' p2' h1) (fun h0 : term1877 _104757 _104758 t'' f' s p1' p2' => @lem4371928 _104757 _104758 t'' f' s p1' p2' h0) (fun h0 : term1871 _104757 _104758 f' s p1' t'' p2' => @lem4372116 _104757 _104758 f' s p1' t'' p2' h0)). Qed.
Lemma lem4372118 {_104757 _104758 _104795 _104796 : Type'} (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1881 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') : False.
Proof. exact (or_elim (@lem4371298 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' h1) (fun h0 : term1879 _104757 _104758 f' s p1' t'' p2' => @lem4372117 _104757 _104758 f' s p1' t'' p2' h0) (fun h0 : term1867 _104795 _104796 f'' t'''' p1'' t''' p2'' => @lem4372115 _104795 _104796 f'' t'''' p1'' t''' p2'' h0)). Qed.
Lemma lem4372119 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1887 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (or_elim (@lem4371310 _104717 _104718 f g t p1 t' p2 h1) (fun h0 : term1851 _104717 f p1 => @lem4372113 _104717 _104718 f g t p1 t' p2 h0 h1) (fun h0 : term1851 _104718 g p2 => @lem4372111 _104717 _104718 f g t p1 t' p2 h0 h1)). Qed.
Lemma lem4372120 {_104717 _104718 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1899 _104717 _104718 f g t p1 t' p2) : False.
Proof. exact (or_elim (@lem4371297 _104717 _104718 f g t p1 t' p2 h1) (fun h0 : term1897 _104717 _104718 t t' f g p1 p2 => @lem4371809 _104717 _104718 t t' f g p1 p2 h0) (fun h0 : term1887 _104717 _104718 f g t p1 t' p2 => @lem4372119 _104717 _104718 f g t p1 t' p2 h0)). Qed.
Lemma lem4372121 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t'''' : _104795 -> Prop) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1807 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'') : False.
Proof. exact (or_elim (@lem4371296 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' h1) (fun h0 : term1899 _104717 _104718 f g t p1 t' p2 => @lem4372120 _104717 _104718 f g t p1 t' p2 h0) (fun h0 : term1881 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' => @lem4372118 _104757 _104758 _104795 _104796 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' h0)). Qed.
Lemma lem4372122 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (p2'' : _104796) (h1 : term1810 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'') : False.
Proof. exact (ex_elim (@lem4370793 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'' h1) (fun t'''' : _104795 -> Prop => fun h0 : term1809 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'' t'''' => @lem4372121 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t'''' p1'' t''' p2'' h0)). Qed.
Lemma lem4372123 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (p1'' : _104795) (t''' : _104796 -> Prop) (h1 : term1812 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''') : False.
Proof. exact (ex_elim (@lem4370792 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' h1) (fun p2'' : _104796 => fun h0 : term1811 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'' => @lem4372122 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' p2'' h0)). Qed.
Lemma lem4372124 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (t''' : _104796 -> Prop) (h1 : term1814 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''') : False.
Proof. exact (ex_elim (@lem4370791 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' h1) (fun p1'' : _104795 => fun h0 : term1813 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' p1'' => @lem4372123 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' p1'' t''' h0)). Qed.
Lemma lem4372125 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (f'' : type686 _104795) (h1 : term1816 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'') : False.
Proof. exact (ex_elim (@lem4370790 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' h1) (fun t''' : _104796 -> Prop => fun h0 : term1815 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' => @lem4372124 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' t''' h0)). Qed.
Lemma lem4372126 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (t'' : _104758 -> Prop) (p2' : _104758) (h1 : term1818 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2') : False.
Proof. exact (ex_elim (@lem4370789 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' h1) (fun f'' : type686 _104795 => fun h0 : term1817 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' => @lem4372125 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' f'' h0)). Qed.
Lemma lem4372127 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (p2' : _104758) (h1 : term1820 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2') : False.
Proof. exact (ex_elim (@lem4370788 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2' h1) (fun t'' : _104758 -> Prop => fun h0 : term1819 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2' t'' => @lem4372126 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' t'' p2' h0)). Qed.
Lemma lem4372128 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (p1' : _104757) (h1 : term1822 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1') : False.
Proof. exact (ex_elim (@lem4370787 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' h1) (fun p2' : _104758 => fun h0 : term1821 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2' => @lem4372127 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' p2' h0)). Qed.
Lemma lem4372129 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (f' : type686 _104758) (s : _104757 -> Prop) (h1 : term1824 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s) : False.
Proof. exact (ex_elim (@lem4370786 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s h1) (fun p1' : _104757 => fun h0 : term1823 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' => @lem4372128 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s p1' h0)). Qed.
Lemma lem4372130 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (s : _104757 -> Prop) (h1 : term1826 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s) : False.
Proof. exact (ex_elim (@lem4370785 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s h1) (fun f' : type686 _104758 => fun h0 : term1825 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s f' => @lem4372129 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 f' s h0)). Qed.
Lemma lem4372131 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (t' : _104718 -> Prop) (p2 : _104718) (h1 : term1828 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2) : False.
Proof. exact (ex_elim (@lem4370784 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 h1) (fun s : _104757 -> Prop => fun h0 : term1827 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s => @lem4372130 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 s h0)). Qed.
Lemma lem4372132 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (t : _104717 -> Prop) (p1 : _104717) (p2 : _104718) (h1 : term1830 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2) : False.
Proof. exact (ex_elim (@lem4370783 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2 h1) (fun t' : _104718 -> Prop => fun h0 : term1829 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2 t' => @lem4372131 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 t' p2 h0)). Qed.
Lemma lem4372133 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (p2 : _104718) (h1 : term1832 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2) : False.
Proof. exact (ex_elim (@lem4370782 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2 h1) (fun t : _104717 -> Prop => fun h0 : term1831 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2 t => @lem4372132 _104717 _104718 _104757 _104758 _104795 _104796 f g t p1 p2 h0)). Qed.
Lemma lem4372134 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (p1 : _104717) (h1 : term1834 _104717 _104718 _104757 _104758 _104795 _104796 f g p1) : False.
Proof. exact (ex_elim (@lem4370781 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 h1) (fun p2 : _104718 => fun h0 : term1833 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2 => @lem4372133 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 p2 h0)). Qed.
Lemma lem4372135 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (g : type686 _104718) (h1 : term1836 _104717 _104718 _104757 _104758 _104795 _104796 f g) : False.
Proof. exact (ex_elim (@lem4370780 _104717 _104718 _104757 _104758 _104795 _104796 f g h1) (fun p1 : _104717 => fun h0 : term1835 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 => @lem4372134 _104717 _104718 _104757 _104758 _104795 _104796 f g p1 h0)). Qed.
Lemma lem4372136 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (f : type686 _104717) (h1 : term1838 _104717 _104718 _104757 _104758 _104795 _104796 f) : False.
Proof. exact (ex_elim (@lem4370779 _104717 _104718 _104757 _104758 _104795 _104796 f h1) (fun g : type686 _104718 => fun h0 : term1837 _104717 _104718 _104757 _104758 _104795 _104796 f g => @lem4372135 _104717 _104718 _104757 _104758 _104795 _104796 f g h0)). Qed.
Lemma lem4372137 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : False.
Proof. exact (ex_elim (@lem4370778 _104717 _104718 _104757 _104758 _104795 _104796 h1) (fun f : type686 _104717 => fun h0 : term1839 _104717 _104718 _104757 _104758 _104795 _104796 f => @lem4372136 _104717 _104718 _104757 _104758 _104795 _104796 f h0)). Qed.
Lemma lem4372138 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : (term419 _104717 _104718 _104757 _104758 _104795 _104796) = False.
Proof. exact (prop_ext (fun h2 : term419 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4372137 _104717 _104718 _104757 _104758 _104795 _104796 h1) (fun h2 : False => @lem4364841 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4372139 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : False.
Proof. exact (EQ_MP (@lem4372138 _104717 _104718 _104757 _104758 _104795 _104796 h1) (@lem4364841 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4372140 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term419 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4372139 _104717 _104718 _104757 _104758 _104795 _104796 h0). Qed.
Lemma lem4372141 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term416 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4364840 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4372140 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4372142 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4364836 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4372141 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4372144 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (@lem4364232 _104717 _104718 _104757 _104758 _104795 _104796 (@lem4372142 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4372145 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : False.
Proof. exact (@lem4372144 _104717 _104718 _104757 _104758 _104795 _104796 (@lem4364216 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4372146 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : (term419 _104717 _104718 _104757 _104758 _104795 _104796) = False.
Proof. exact (prop_ext (fun h2 : term419 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4372145 _104717 _104718 _104757 _104758 _104795 _104796 h1) (fun h2 : False => @lem4364216 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4372147 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} (h1 : term419 _104717 _104718 _104757 _104758 _104795 _104796) : False.
Proof. exact (EQ_MP (@lem4372146 _104717 _104718 _104757 _104758 _104795 _104796 h1) (@lem4364216 _104717 _104718 _104757 _104758 _104795 _104796 h1)). Qed.
Lemma lem4372148 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term418 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (fun h0 : term419 _104717 _104718 _104757 _104758 _104795 _104796 => @lem4372147 _104717 _104718 _104757 _104758 _104795 _104796 h0). Qed.
Lemma lem4372149 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term416 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4364215 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4372148 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4372151 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term356 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4364211 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4372149 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
Lemma lem4372152 {_104717 _104718 _104757 _104758 _104795 _104796 : Type'} : term355 _104717 _104718 _104757 _104758 _104795 _104796.
Proof. exact (EQ_MP (@lem4363655 _104717 _104718 _104757 _104758 _104795 _104796) (@lem4372151 _104717 _104718 _104757 _104758 _104795 _104796)). Qed.
