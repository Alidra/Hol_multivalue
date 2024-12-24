Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BOUND_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LT_IMP_LE_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import NSUM_BOUND_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem6975628 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6975629 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem6975630 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem6975629 t1) (@lem6975628 t1)). Qed.
Lemma lem6975631 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem6975630 t1 t2). Qed.
Lemma lem6975632 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem6975633 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem6975632 t1 t2) (@lem6975631 t1 t2)). Qed.
Lemma lem6975634 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem6975633 t1 t2 t3). Qed.
Lemma lem6975635 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem6975636 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem6975635 t1 t2 t3) (@lem6975634 t1 t2 t3)). Qed.
Lemma lem6975637 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem6975636 t1 t2 t3)). Qed.
Lemma lem6975639 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6975640 {_128066 : Type'} : (term8 _128066) = (term9 _128066).
Proof. exact (@lem6975639 (term8 _128066)). Qed.
Lemma lem6975641 {_128066 : Type'} : (term9 _128066) = (term8 _128066).
Proof. exact (SYM (@lem6975640 _128066)). Qed.
Lemma lem6975642 {_128066 : Type'} (h1 : term10 _128066) : term10 _128066.
Proof. exact (h1). Qed.
Lemma lem6975643 {_128066 : Type'} : term11 _128066.
Proof. exact (@lem3216368 _128066). Qed.
Lemma lem6975646 {_128066 : Type'} : term12 _128066.
Proof. exact (@lem6975627 _128066). Qed.
Lemma lem6975652 {_128066 A : Type'} (h1 : term13 _128066 A) : term13 _128066 A.
Proof. exact (h1). Qed.
Lemma lem6975653 {_128066 A : Type'} : term14 _128066 A.
Proof. exact (fun h0 : term13 _128066 A => @lem6975652 _128066 A h0). Qed.
Lemma lem6975654 {_128066 A : Type'} (h1 : term14 _128066 A) : term14 _128066 A.
Proof. exact (h1). Qed.
Lemma lem6975655 {_128066 A : Type'} (h1 : term13 _128066 A) : term13 _128066 A.
Proof. exact (h1). Qed.
Lemma lem6975656 {_128066 A : Type'} (h1 : term13 _128066 A) (h2 : term14 _128066 A) : term13 _128066 A.
Proof. exact (@lem6975654 _128066 A h2 (@lem6975655 _128066 A h1)). Qed.
Lemma lem6975657 {_128066 A : Type'} (h1 : term13 _128066 A) : term15 _128066 A.
Proof. exact (fun h0 : term14 _128066 A => @lem6975656 _128066 A h1 h0). Qed.
Lemma lem6975658 {_128066 A : Type'} (h1 : term14 _128066 A) : term14 _128066 A.
Proof. exact (h1). Qed.
Lemma lem6975659 {_128066 A : Type'} (h1 : term13 _128066 A) (h2 : term14 _128066 A) : term13 _128066 A.
Proof. exact (@lem6975657 _128066 A h1 (@lem6975658 _128066 A h2)). Qed.
Lemma lem6975660 {_128066 A : Type'} (h1 : term14 _128066 A) : term14 _128066 A.
Proof. exact (fun h0 : term13 _128066 A => @lem6975659 _128066 A h0 h1). Qed.
Lemma lem6975661 {_128066 A : Type'} : term16 _128066 A.
Proof. exact (fun h0 : term14 _128066 A => @lem6975660 _128066 A h0). Qed.
Lemma lem6975664 {_128066 A : Type'} : term14 _128066 A.
Proof. exact (@lem6975661 _128066 A (@lem6975653 _128066 A)). Qed.
Lemma lem6975665 {_128066 A : Type'} : term14 _128066 A.
Proof. exact (@lem6975664 _128066 A). Qed.
Lemma lem6975857 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6975858 {_128066 : Type'} : (term17 _128066) = (term18 _128066).
Proof. exact (@lem6975857 (term11 _128066)). Qed.
Lemma lem6975867 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem6975868 {_128066 : Type'} : (term20 _128066) = (term21 _128066).
Proof. exact (MK_COMB (@lem6975867) (@lem6975858 _128066)). Qed.
Lemma lem6975871 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem6975872 {_128066 A : Type'} : (term23 _128066 A) = (term24 _128066 A).
Proof. exact (MK_COMB (@lem6975871 A) (@lem6975868 _128066)). Qed.
Lemma lem6975875 {_128066 : Type'} : (term22 _128066) = (term22 _128066).
Proof. exact (eq_refl (term22 _128066)). Qed.
Lemma lem6975876 {_128066 A : Type'} : (term25 _128066 A) = (term26 _128066 A).
Proof. exact (MK_COMB (@lem6975875 _128066) (@lem6975872 _128066 A)). Qed.
Lemma lem6975879 {_128066 : Type'} : (term27 _128066) = (term27 _128066).
Proof. exact (eq_refl (term27 _128066)). Qed.
Lemma lem6975886 {_128066 A : Type'} : (term13 _128066 A) = (term28 _128066 A).
Proof. exact (MK_COMB (@lem6975879 _128066) (@lem6975876 _128066 A)). Qed.
Lemma lem6975889 {_128066 : Type'} (s : _128066 -> Prop) : (term29 _128066 s) = (term29 _128066 s).
Proof. exact (eq_refl (term29 _128066 s)). Qed.
Lemma lem6975890 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (@IN _128066 x s).
Proof. exact (eq_refl (@IN _128066 x s)). Qed.
Lemma lem6975891 {_128066 : Type'} (s : _128066 -> Prop) : (term30 _128066 s) = (term30 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6975890 _128066 x s)). Qed.
Lemma lem6975892 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6975893 {_128066 : Type'} (s : _128066 -> Prop) : (term31 _128066 s) = (term31 _128066 s).
Proof. exact (MK_COMB (@lem6975892 _128066) (@lem6975891 _128066 s)). Qed.
Lemma lem6975894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6975895 {_128066 : Type'} (s : _128066 -> Prop) : (term32 _128066 s) = (term32 _128066 s).
Proof. exact (MK_COMB (@lem6975894) (@lem6975893 _128066 s)). Qed.
Lemma lem6975896 {_128066 : Type'} (s : _128066 -> Prop) : ((term31 _128066 s) = (term29 _128066 s)) = ((term31 _128066 s) = (term29 _128066 s)).
Proof. exact (MK_COMB (@lem6975895 _128066 s) (@lem6975889 _128066 s)). Qed.
Lemma lem6975897 {_128066 : Type'} : (term33 _128066) = (term33 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6975896 _128066 s)). Qed.
Lemma lem6975898 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6975899 {_128066 : Type'} : (term11 _128066) = (term11 _128066).
Proof. exact (MK_COMB (@lem6975898 _128066) (@lem6975897 _128066)). Qed.
Lemma lem6975900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6975901 {_128066 : Type'} : (term18 _128066) = (term18 _128066).
Proof. exact (MK_COMB (@lem6975900) (@lem6975899 _128066)). Qed.
Lemma lem6975906 (m : nat) (n : nat) : (term34 m n) = (term34 m n).
Proof. exact (eq_refl (term34 m n)). Qed.
Lemma lem6975907 (m : nat) : (term35 m) = (term35 m).
Proof. exact (fun_ext (fun n : nat => @lem6975906 m n)). Qed.
Lemma lem6975908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975909 (m : nat) : (term36 m) = (term36 m).
Proof. exact (MK_COMB (@lem6975908) (@lem6975907 m)). Qed.
Lemma lem6975910 : term37 = term37.
Proof. exact (fun_ext (fun m : nat => @lem6975909 m)). Qed.
Lemma lem6975911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975912 : term38 = term38.
Proof. exact (MK_COMB (@lem6975911) (@lem6975910)). Qed.
Lemma lem6975913 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975914 : term19 = term19.
Proof. exact (MK_COMB (@lem6975913) (@lem6975912)). Qed.
Lemma lem6975915 {_128066 : Type'} : (term21 _128066) = (term21 _128066).
Proof. exact (MK_COMB (@lem6975914) (@lem6975901 _128066)). Qed.
Lemma lem6975916 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem6975921 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term40 A s f x b) = (term40 A s f x b).
Proof. exact (eq_refl (term40 A s f x b)). Qed.
Lemma lem6975922 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term41 A s f b) = (term41 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975921 A s f x b)). Qed.
Lemma lem6975923 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6975924 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term42 A s f b) = (term42 A s f b).
Proof. exact (MK_COMB (@lem6975923 A) (@lem6975922 A s f b)). Qed.
Lemma lem6975929 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term43 A s f x b) = (term43 A s f x b).
Proof. exact (eq_refl (term43 A s f x b)). Qed.
Lemma lem6975930 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term44 A s f b) = (term44 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6975929 A s f x b)). Qed.
Lemma lem6975931 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6975932 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term45 A s f b) = (term45 A s f b).
Proof. exact (MK_COMB (@lem6975931 A) (@lem6975930 A s f b)). Qed.
Lemma lem6975933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6975934 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term46 A s f b) = (term46 A s f b).
Proof. exact (MK_COMB (@lem6975933) (@lem6975932 A s f b)). Qed.
Lemma lem6975935 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term47 A s f b) = (term47 A s f b).
Proof. exact (MK_COMB (@lem6975934 A s f b) (@lem6975924 A s f b)). Qed.
Lemma lem6975938 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (eq_refl (term48 A s)). Qed.
Lemma lem6975939 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term49 A s f b) = (term49 A s f b).
Proof. exact (MK_COMB (@lem6975938 A s) (@lem6975935 A s f b)). Qed.
Lemma lem6975940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975941 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term50 A s f b) = (term50 A s f b).
Proof. exact (MK_COMB (@lem6975940) (@lem6975939 A s f b)). Qed.
Lemma lem6975942 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term51 A f s b) = (term51 A f s b).
Proof. exact (MK_COMB (@lem6975941 A s f b) (@lem6975916 A f s b)). Qed.
Lemma lem6975943 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term52 A f s) = (term52 A f s).
Proof. exact (fun_ext (fun b : nat => @lem6975942 A f s b)). Qed.
Lemma lem6975944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975945 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term53 A f s) = (term53 A f s).
Proof. exact (MK_COMB (@lem6975944) (@lem6975943 A f s)). Qed.
Lemma lem6975946 {A : Type'} (s : A -> Prop) : (term54 A s) = (term54 A s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6975945 A f s)). Qed.
Lemma lem6975947 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6975948 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem6975947 A) (@lem6975946 A s)). Qed.
Lemma lem6975949 {A : Type'} : (term56 A) = (term56 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6975948 A s)). Qed.
Lemma lem6975950 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6975951 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem6975950 A) (@lem6975949 A)). Qed.
Lemma lem6975952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975953 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem6975952) (@lem6975951 A)). Qed.
Lemma lem6975954 {_128066 A : Type'} : (term24 _128066 A) = (term24 _128066 A).
Proof. exact (MK_COMB (@lem6975953 A) (@lem6975915 _128066)). Qed.
Lemma lem6975955 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6975960 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term40 _128066 s f x b) = (term40 _128066 s f x b).
Proof. exact (eq_refl (term40 _128066 s f x b)). Qed.
Lemma lem6975961 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term41 _128066 s f b) = (term41 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6975960 _128066 s f x b)). Qed.
Lemma lem6975962 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6975963 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term42 _128066 s f b) = (term42 _128066 s f b).
Proof. exact (MK_COMB (@lem6975962 _128066) (@lem6975961 _128066 s f b)). Qed.
Lemma lem6975968 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term43 _128066 s f x b) = (term43 _128066 s f x b).
Proof. exact (eq_refl (term43 _128066 s f x b)). Qed.
Lemma lem6975969 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term44 _128066 s f b) = (term44 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6975968 _128066 s f x b)). Qed.
Lemma lem6975970 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6975971 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term45 _128066 s f b) = (term45 _128066 s f b).
Proof. exact (MK_COMB (@lem6975970 _128066) (@lem6975969 _128066 s f b)). Qed.
Lemma lem6975972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6975973 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term46 _128066 s f b) = (term46 _128066 s f b).
Proof. exact (MK_COMB (@lem6975972) (@lem6975971 _128066 s f b)). Qed.
Lemma lem6975974 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term47 _128066 s f b) = (term47 _128066 s f b).
Proof. exact (MK_COMB (@lem6975973 _128066 s f b) (@lem6975963 _128066 s f b)). Qed.
Lemma lem6975977 {_128066 : Type'} (s : _128066 -> Prop) : (term48 _128066 s) = (term48 _128066 s).
Proof. exact (eq_refl (term48 _128066 s)). Qed.
Lemma lem6975978 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term49 _128066 s f b) = (term49 _128066 s f b).
Proof. exact (MK_COMB (@lem6975977 _128066 s) (@lem6975974 _128066 s f b)). Qed.
Lemma lem6975979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975980 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term50 _128066 s f b) = (term50 _128066 s f b).
Proof. exact (MK_COMB (@lem6975979) (@lem6975978 _128066 s f b)). Qed.
Lemma lem6975981 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term51 _128066 f s b) = (term51 _128066 f s b).
Proof. exact (MK_COMB (@lem6975980 _128066 s f b) (@lem6975955 _128066 f s b)). Qed.
Lemma lem6975982 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term52 _128066 f s) = (term52 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6975981 _128066 f s b)). Qed.
Lemma lem6975983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6975984 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term53 _128066 f s) = (term53 _128066 f s).
Proof. exact (MK_COMB (@lem6975983) (@lem6975982 _128066 f s)). Qed.
Lemma lem6975985 {_128066 : Type'} (s : _128066 -> Prop) : (term54 _128066 s) = (term54 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6975984 _128066 f s)). Qed.
Lemma lem6975986 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6975987 {_128066 : Type'} (s : _128066 -> Prop) : (term55 _128066 s) = (term55 _128066 s).
Proof. exact (MK_COMB (@lem6975986 _128066) (@lem6975985 _128066 s)). Qed.
Lemma lem6975988 {_128066 : Type'} : (term56 _128066) = (term56 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6975987 _128066 s)). Qed.
Lemma lem6975989 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6975990 {_128066 : Type'} : (term12 _128066) = (term12 _128066).
Proof. exact (MK_COMB (@lem6975989 _128066) (@lem6975988 _128066)). Qed.
Lemma lem6975991 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6975992 {_128066 : Type'} : (term22 _128066) = (term22 _128066).
Proof. exact (MK_COMB (@lem6975991) (@lem6975990 _128066)). Qed.
Lemma lem6975993 {_128066 A : Type'} : (term26 _128066 A) = (term26 _128066 A).
Proof. exact (MK_COMB (@lem6975992 _128066) (@lem6975954 _128066 A)). Qed.
Lemma lem6975994 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6975999 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term57 _128066 s f x b) = (term57 _128066 s f x b).
Proof. exact (eq_refl (term57 _128066 s f x b)). Qed.
Lemma lem6976000 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term58 _128066 s f b) = (term58 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6975999 _128066 s f x b)). Qed.
Lemma lem6976001 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6976002 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term59 _128066 s f b) = (term59 _128066 s f b).
Proof. exact (MK_COMB (@lem6976001 _128066) (@lem6976000 _128066 s f b)). Qed.
Lemma lem6976007 {_128066 : Type'} (s : _128066 -> Prop) : (term60 _128066 s) = (term60 _128066 s).
Proof. exact (eq_refl (term60 _128066 s)). Qed.
Lemma lem6976008 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term61 _128066 s f b) = (term61 _128066 s f b).
Proof. exact (MK_COMB (@lem6976007 _128066 s) (@lem6976002 _128066 s f b)). Qed.
Lemma lem6976011 {_128066 : Type'} (s : _128066 -> Prop) : (term48 _128066 s) = (term48 _128066 s).
Proof. exact (eq_refl (term48 _128066 s)). Qed.
Lemma lem6976012 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term62 _128066 s f b) = (term62 _128066 s f b).
Proof. exact (MK_COMB (@lem6976011 _128066 s) (@lem6976008 _128066 s f b)). Qed.
Lemma lem6976013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6976014 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term63 _128066 s f b) = (term63 _128066 s f b).
Proof. exact (MK_COMB (@lem6976013) (@lem6976012 _128066 s f b)). Qed.
Lemma lem6976015 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term64 _128066 f s b) = (term64 _128066 f s b).
Proof. exact (MK_COMB (@lem6976014 _128066 s f b) (@lem6975994 _128066 f s b)). Qed.
Lemma lem6976016 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term65 _128066 f s) = (term65 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6976015 _128066 f s b)). Qed.
Lemma lem6976017 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976018 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term66 _128066 f s) = (term66 _128066 f s).
Proof. exact (MK_COMB (@lem6976017) (@lem6976016 _128066 f s)). Qed.
Lemma lem6976019 {_128066 : Type'} (s : _128066 -> Prop) : (term67 _128066 s) = (term67 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976018 _128066 f s)). Qed.
Lemma lem6976020 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6976021 {_128066 : Type'} (s : _128066 -> Prop) : (term68 _128066 s) = (term68 _128066 s).
Proof. exact (MK_COMB (@lem6976020 _128066) (@lem6976019 _128066 s)). Qed.
Lemma lem6976022 {_128066 : Type'} : (term69 _128066) = (term69 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976021 _128066 s)). Qed.
Lemma lem6976023 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6976024 {_128066 : Type'} : (term8 _128066) = (term8 _128066).
Proof. exact (MK_COMB (@lem6976023 _128066) (@lem6976022 _128066)). Qed.
Lemma lem6976025 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976026 {_128066 : Type'} : (term10 _128066) = (term10 _128066).
Proof. exact (MK_COMB (@lem6976025) (@lem6976024 _128066)). Qed.
Lemma lem6976027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6976028 {_128066 : Type'} : (term27 _128066) = (term27 _128066).
Proof. exact (MK_COMB (@lem6976027) (@lem6976026 _128066)). Qed.
Lemma lem6976029 {_128066 A : Type'} : (term28 _128066 A) = (term28 _128066 A).
Proof. exact (MK_COMB (@lem6976028 _128066) (@lem6975993 _128066 A)). Qed.
Lemma lem6976178 {_128066 A : Type'} : (term13 _128066 A) = (term28 _128066 A).
Proof. exact (TRANS (@lem6975886 _128066 A) (@lem6976029 _128066 A)). Qed.
Lemma lem6976179 {_128066 A : Type'} : (term28 _128066 A) = (term13 _128066 A).
Proof. exact (SYM (@lem6976178 _128066 A)). Qed.
Lemma lem6976180 {_128066 : Type'} (h1 : term10 _128066) : term10 _128066.
Proof. exact (h1). Qed.
Lemma lem6976181 {_128066 : Type'} (h1 : term12 _128066) : term12 _128066.
Proof. exact (h1). Qed.
Lemma lem6976182 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem6976183 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem6976184 {_128066 : Type'} (h1 : term11 _128066) : term11 _128066.
Proof. exact (h1). Qed.
Lemma lem6976193 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term57 _128066 s f x b) = (term70 _128066 s f x b).
Proof. exact (@lem17265 (@IN _128066 x s) (term71 _128066 f x b)). Qed.
Lemma lem6976194 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term58 _128066 s f b) = (term72 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976193 _128066 s f x b)). Qed.
Lemma lem6976195 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6976196 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term59 _128066 s f b) = (term73 _128066 s f b).
Proof. exact (MK_COMB (@lem6976195 _128066) (@lem6976194 _128066 s f b)). Qed.
Lemma lem6976198 {_128066 : Type'} (s : _128066 -> Prop) : (term60 _128066 s) = (term60 _128066 s).
Proof. exact (eq_refl (term60 _128066 s)). Qed.
Lemma lem6976199 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term61 _128066 s f b) = (term74 _128066 s f b).
Proof. exact (MK_COMB (@lem6976198 _128066 s) (@lem6976196 _128066 s f b)). Qed.
Lemma lem6976201 {_128066 : Type'} (s : _128066 -> Prop) : (term48 _128066 s) = (term48 _128066 s).
Proof. exact (eq_refl (term48 _128066 s)). Qed.
Lemma lem6976202 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term62 _128066 s f b) = (term75 _128066 s f b).
Proof. exact (MK_COMB (@lem6976201 _128066 s) (@lem6976199 _128066 s f b)). Qed.
Lemma lem6976203 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term76 _128066 f s b) = (term76 _128066 f s b).
Proof. exact (eq_refl (term76 _128066 f s b)). Qed.
Lemma lem6976204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6976205 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term77 _128066 s f b) = (term78 _128066 s f b).
Proof. exact (MK_COMB (@lem6976204) (@lem6976202 _128066 s f b)). Qed.
Lemma lem6976206 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term79 _128066 f s b) = (term80 _128066 f s b).
Proof. exact (MK_COMB (@lem6976205 _128066 s f b) (@lem6976203 _128066 f s b)). Qed.
Lemma lem6976207 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term81 _128066 f s b) = (term79 _128066 f s b).
Proof. exact (@lem17362 (term62 _128066 s f b) (term39 _128066 f s b)). Qed.
Lemma lem6976208 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term81 _128066 f s b) = (term80 _128066 f s b).
Proof. exact (TRANS (@lem6976207 _128066 f s b) (@lem6976206 _128066 f s b)). Qed.
Lemma lem6976209 (P : nat -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem6976210 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term84 _128066 f s) = (term85 _128066 f s).
Proof. exact (@lem6976209 (term65 _128066 f s)). Qed.
Lemma lem6976211 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term86 _128066 f s b) = (term64 _128066 f s b).
Proof. exact (eq_refl (term86 _128066 f s b)). Qed.
Lemma lem6976212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976213 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term87 _128066 f s b) = (term81 _128066 f s b).
Proof. exact (MK_COMB (@lem6976212) (@lem6976211 _128066 f s b)). Qed.
Lemma lem6976214 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term87 _128066 f s b) = (term80 _128066 f s b).
Proof. exact (TRANS (@lem6976213 _128066 f s b) (@lem6976208 _128066 f s b)). Qed.
Lemma lem6976215 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term88 _128066 f s) = (term89 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6976214 _128066 f s b)). Qed.
Lemma lem6976216 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem6976217 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term85 _128066 f s) = (term90 _128066 f s).
Proof. exact (MK_COMB (@lem6976216) (@lem6976215 _128066 f s)). Qed.
Lemma lem6976218 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term84 _128066 f s) = (term90 _128066 f s).
Proof. exact (TRANS (@lem6976210 _128066 f s) (@lem6976217 _128066 f s)). Qed.
Lemma lem6976219 {_128066 : Type'} (P : type704 _128066) : (term91 _128066 P) = (term92 _128066 P).
Proof. exact (@lem18392 (_128066 -> nat) P). Qed.
Lemma lem6976220 {_128066 : Type'} (s : _128066 -> Prop) : (term93 _128066 s) = (term94 _128066 s).
Proof. exact (@lem6976219 _128066 (term67 _128066 s)). Qed.
Lemma lem6976221 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term95 _128066 s f) = (term66 _128066 f s).
Proof. exact (eq_refl (term95 _128066 s f)). Qed.
Lemma lem6976222 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976223 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term96 _128066 s f) = (term84 _128066 f s).
Proof. exact (MK_COMB (@lem6976222) (@lem6976221 _128066 f s)). Qed.
Lemma lem6976224 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term96 _128066 s f) = (term90 _128066 f s).
Proof. exact (TRANS (@lem6976223 _128066 f s) (@lem6976218 _128066 f s)). Qed.
Lemma lem6976225 {_128066 : Type'} (s : _128066 -> Prop) : (term97 _128066 s) = (term98 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976224 _128066 f s)). Qed.
Lemma lem6976226 {_128066 : Type'} : (@ex (_128066 -> nat)) = (@ex (_128066 -> nat)).
Proof. exact (eq_refl (@ex (_128066 -> nat))). Qed.
Lemma lem6976227 {_128066 : Type'} (s : _128066 -> Prop) : (term94 _128066 s) = (term99 _128066 s).
Proof. exact (MK_COMB (@lem6976226 _128066) (@lem6976225 _128066 s)). Qed.
Lemma lem6976228 {_128066 : Type'} (s : _128066 -> Prop) : (term93 _128066 s) = (term99 _128066 s).
Proof. exact (TRANS (@lem6976220 _128066 s) (@lem6976227 _128066 s)). Qed.
Lemma lem6976229 {_128066 : Type'} (P : type686 _128066) : (term100 _128066 P) = (term101 _128066 P).
Proof. exact (@lem18392 (_128066 -> Prop) P). Qed.
Lemma lem6976230 {_128066 : Type'} : (term10 _128066) = (term102 _128066).
Proof. exact (@lem6976229 _128066 (term69 _128066)). Qed.
Lemma lem6976231 {_128066 : Type'} (s : _128066 -> Prop) : (term103 _128066 s) = (term68 _128066 s).
Proof. exact (eq_refl (term103 _128066 s)). Qed.
Lemma lem6976232 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976233 {_128066 : Type'} (s : _128066 -> Prop) : (term104 _128066 s) = (term93 _128066 s).
Proof. exact (MK_COMB (@lem6976232) (@lem6976231 _128066 s)). Qed.
Lemma lem6976234 {_128066 : Type'} (s : _128066 -> Prop) : (term104 _128066 s) = (term99 _128066 s).
Proof. exact (TRANS (@lem6976233 _128066 s) (@lem6976228 _128066 s)). Qed.
Lemma lem6976235 {_128066 : Type'} : (term105 _128066) = (term106 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976234 _128066 s)). Qed.
Lemma lem6976236 {_128066 : Type'} : (@ex (_128066 -> Prop)) = (@ex (_128066 -> Prop)).
Proof. exact (eq_refl (@ex (_128066 -> Prop))). Qed.
Lemma lem6976237 {_128066 : Type'} : (term102 _128066) = (term107 _128066).
Proof. exact (MK_COMB (@lem6976236 _128066) (@lem6976235 _128066)). Qed.
Lemma lem6976346 {_128066 : Type'} : (term10 _128066) = (term107 _128066).
Proof. exact (TRANS (@lem6976230 _128066) (@lem6976237 _128066)). Qed.
Lemma lem6976347 {_128066 : Type'} (h1 : term10 _128066) : term107 _128066.
Proof. exact (EQ_MP (@lem6976346 _128066) (@lem6976180 _128066 h1)). Qed.
Lemma lem6976355 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term108 _128066 s f x b) = (term109 _128066 s f x b).
Proof. exact (@lem17362 (@IN _128066 x s) (term110 _128066 f x b)). Qed.
Lemma lem6976356 {_128066 : Type'} (P : _128066 -> Prop) : (term111 _128066 P) = (term112 _128066 P).
Proof. exact (@lem18392 _128066 P). Qed.
Lemma lem6976357 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term113 _128066 s f b) = (term114 _128066 s f b).
Proof. exact (@lem6976356 _128066 (term44 _128066 s f b)). Qed.
Lemma lem6976358 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term115 _128066 s f b x) = (term43 _128066 s f x b).
Proof. exact (eq_refl (term115 _128066 s f b x)). Qed.
Lemma lem6976359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976360 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term116 _128066 s f b x) = (term108 _128066 s f x b).
Proof. exact (MK_COMB (@lem6976359) (@lem6976358 _128066 s f x b)). Qed.
Lemma lem6976361 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term116 _128066 s f b x) = (term109 _128066 s f x b).
Proof. exact (TRANS (@lem6976360 _128066 s f x b) (@lem6976355 _128066 s f x b)). Qed.
Lemma lem6976362 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term117 _128066 s f b) = (term118 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976361 _128066 s f x b)). Qed.
Lemma lem6976363 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976364 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term114 _128066 s f b) = (term119 _128066 s f b).
Proof. exact (MK_COMB (@lem6976363 _128066) (@lem6976362 _128066 s f b)). Qed.
Lemma lem6976365 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term113 _128066 s f b) = (term119 _128066 s f b).
Proof. exact (TRANS (@lem6976357 _128066 s f b) (@lem6976364 _128066 s f b)). Qed.
Lemma lem6976372 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term120 _128066 s f x b) = (term121 _128066 s f x b).
Proof. exact (@lem17045 (@IN _128066 x s) (term71 _128066 f x b)). Qed.
Lemma lem6976373 {_128066 : Type'} (P : _128066 -> Prop) : (term122 _128066 P) = (term123 _128066 P).
Proof. exact (@lem18394 _128066 P). Qed.
Lemma lem6976374 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term124 _128066 s f b) = (term125 _128066 s f b).
Proof. exact (@lem6976373 _128066 (term41 _128066 s f b)). Qed.
Lemma lem6976375 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term126 _128066 s f b x) = (term40 _128066 s f x b).
Proof. exact (eq_refl (term126 _128066 s f b x)). Qed.
Lemma lem6976376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976377 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term127 _128066 s f b x) = (term120 _128066 s f x b).
Proof. exact (MK_COMB (@lem6976376) (@lem6976375 _128066 s f x b)). Qed.
Lemma lem6976378 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term127 _128066 s f b x) = (term121 _128066 s f x b).
Proof. exact (TRANS (@lem6976377 _128066 s f x b) (@lem6976372 _128066 s f x b)). Qed.
Lemma lem6976379 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term128 _128066 s f b) = (term129 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976378 _128066 s f x b)). Qed.
Lemma lem6976380 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6976381 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term125 _128066 s f b) = (term130 _128066 s f b).
Proof. exact (MK_COMB (@lem6976380 _128066) (@lem6976379 _128066 s f b)). Qed.
Lemma lem6976382 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term124 _128066 s f b) = (term130 _128066 s f b).
Proof. exact (TRANS (@lem6976374 _128066 s f b) (@lem6976381 _128066 s f b)). Qed.
Lemma lem6976383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976384 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term131 _128066 s f b) = (term132 _128066 s f b).
Proof. exact (MK_COMB (@lem6976383) (@lem6976365 _128066 s f b)). Qed.
Lemma lem6976385 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term133 _128066 s f b) = (term134 _128066 s f b).
Proof. exact (MK_COMB (@lem6976384 _128066 s f b) (@lem6976382 _128066 s f b)). Qed.
Lemma lem6976386 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term135 _128066 s f b) = (term133 _128066 s f b).
Proof. exact (@lem17045 (term45 _128066 s f b) (term42 _128066 s f b)). Qed.
Lemma lem6976387 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term135 _128066 s f b) = (term134 _128066 s f b).
Proof. exact (TRANS (@lem6976386 _128066 s f b) (@lem6976385 _128066 s f b)). Qed.
Lemma lem6976389 {_128066 : Type'} (s : _128066 -> Prop) : (term136 _128066 s) = (term136 _128066 s).
Proof. exact (eq_refl (term136 _128066 s)). Qed.
Lemma lem6976390 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term137 _128066 s f b) = (term138 _128066 s f b).
Proof. exact (MK_COMB (@lem6976389 _128066 s) (@lem6976387 _128066 s f b)). Qed.
Lemma lem6976391 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term139 _128066 s f b) = (term137 _128066 s f b).
Proof. exact (@lem17045 (@FINITE _128066 s) (term47 _128066 s f b)). Qed.
Lemma lem6976392 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term139 _128066 s f b) = (term138 _128066 s f b).
Proof. exact (TRANS (@lem6976391 _128066 s f b) (@lem6976390 _128066 s f b)). Qed.
Lemma lem6976393 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6976394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976395 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term140 _128066 s f b) = (term141 _128066 s f b).
Proof. exact (MK_COMB (@lem6976394) (@lem6976392 _128066 s f b)). Qed.
Lemma lem6976396 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term142 _128066 f s b) = (term143 _128066 f s b).
Proof. exact (MK_COMB (@lem6976395 _128066 s f b) (@lem6976393 _128066 f s b)). Qed.
Lemma lem6976397 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term51 _128066 f s b) = (term142 _128066 f s b).
Proof. exact (@lem17265 (term49 _128066 s f b) (term39 _128066 f s b)). Qed.
Lemma lem6976398 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term51 _128066 f s b) = (term143 _128066 f s b).
Proof. exact (TRANS (@lem6976397 _128066 f s b) (@lem6976396 _128066 f s b)). Qed.
Lemma lem6976399 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term52 _128066 f s) = (term144 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6976398 _128066 f s b)). Qed.
Lemma lem6976400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976401 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term53 _128066 f s) = (term145 _128066 f s).
Proof. exact (MK_COMB (@lem6976400) (@lem6976399 _128066 f s)). Qed.
Lemma lem6976402 {_128066 : Type'} (s : _128066 -> Prop) : (term54 _128066 s) = (term146 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976401 _128066 f s)). Qed.
Lemma lem6976403 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6976404 {_128066 : Type'} (s : _128066 -> Prop) : (term55 _128066 s) = (term147 _128066 s).
Proof. exact (MK_COMB (@lem6976403 _128066) (@lem6976402 _128066 s)). Qed.
Lemma lem6976405 {_128066 : Type'} : (term56 _128066) = (term148 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976404 _128066 s)). Qed.
Lemma lem6976406 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6976407 {_128066 : Type'} : (term12 _128066) = (term149 _128066).
Proof. exact (MK_COMB (@lem6976406 _128066) (@lem6976405 _128066)). Qed.
Lemma lem6976562 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6976563 {_128066 : Type'} (P : _128066 -> Prop) (Q : Prop) : (term150 _128066 P Q) = (term151 _128066 P Q).
Proof. exact (@lem6976562 _128066 P Q). Qed.
Lemma lem6976564 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term152 _128066 s f b) = (term153 _128066 s f b).
Proof. exact (@lem6976563 _128066 (term118 _128066 s f b) (term130 _128066 s f b)). Qed.
Lemma lem6976565 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term154 _128066 s f b x) = (term109 _128066 s f x b).
Proof. exact (eq_refl (term154 _128066 s f b x)). Qed.
Lemma lem6976566 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term155 _128066 s f b) = (term118 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976565 _128066 s f x b)). Qed.
Lemma lem6976567 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976568 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term156 _128066 s f b) = (term119 _128066 s f b).
Proof. exact (MK_COMB (@lem6976567 _128066) (@lem6976566 _128066 s f b)). Qed.
Lemma lem6976569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976570 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term157 _128066 s f b) = (term132 _128066 s f b).
Proof. exact (MK_COMB (@lem6976569) (@lem6976568 _128066 s f b)). Qed.
Lemma lem6976571 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term130 _128066 s f b) = (term130 _128066 s f b).
Proof. exact (eq_refl (term130 _128066 s f b)). Qed.
Lemma lem6976572 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term152 _128066 s f b) = (term134 _128066 s f b).
Proof. exact (MK_COMB (@lem6976570 _128066 s f b) (@lem6976571 _128066 s f b)). Qed.
Lemma lem6976573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976574 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term158 _128066 s f b) = (term159 _128066 s f b).
Proof. exact (MK_COMB (@lem6976573) (@lem6976572 _128066 s f b)). Qed.
Lemma lem6976575 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term154 _128066 s f b x) = (term109 _128066 s f x b).
Proof. exact (eq_refl (term154 _128066 s f b x)). Qed.
Lemma lem6976576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976577 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term160 _128066 s f b x) = (term161 _128066 s f x b).
Proof. exact (MK_COMB (@lem6976576) (@lem6976575 _128066 s f x b)). Qed.
Lemma lem6976578 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term130 _128066 s f b) = (term130 _128066 s f b).
Proof. exact (eq_refl (term130 _128066 s f b)). Qed.
Lemma lem6976579 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term162 _128066 x s f b) = (term163 _128066 x s f b).
Proof. exact (MK_COMB (@lem6976577 _128066 s f x b) (@lem6976578 _128066 s f b)). Qed.
Lemma lem6976580 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term164 _128066 s f b) = (term165 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976579 _128066 x s f b)). Qed.
Lemma lem6976581 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976582 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term153 _128066 s f b) = (term166 _128066 s f b).
Proof. exact (MK_COMB (@lem6976581 _128066) (@lem6976580 _128066 s f b)). Qed.
Lemma lem6976583 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : ((term152 _128066 s f b) = (term153 _128066 s f b)) = ((term134 _128066 s f b) = (term166 _128066 s f b)).
Proof. exact (MK_COMB (@lem6976574 _128066 s f b) (@lem6976582 _128066 s f b)). Qed.
Lemma lem6976584 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term134 _128066 s f b) = (term166 _128066 s f b).
Proof. exact (EQ_MP (@lem6976583 _128066 s f b) (@lem6976564 _128066 s f b)). Qed.
Lemma lem6976585 {_128066 : Type'} (s : _128066 -> Prop) : (term136 _128066 s) = (term136 _128066 s).
Proof. exact (eq_refl (term136 _128066 s)). Qed.
Lemma lem6976586 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term138 _128066 s f b) = (term167 _128066 s f b).
Proof. exact (MK_COMB (@lem6976585 _128066 s) (@lem6976584 _128066 s f b)). Qed.
Lemma lem6976588 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6976589 {_128066 : Type'} (P : Prop) (Q : _128066 -> Prop) : (term168 _128066 P Q) = (term169 _128066 P Q).
Proof. exact (@lem6976588 _128066 P Q). Qed.
Lemma lem6976590 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term170 _128066 s f b) = (term171 _128066 s f b).
Proof. exact (@lem6976589 _128066 (term172 _128066 s) (term165 _128066 s f b)). Qed.
Lemma lem6976591 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term173 _128066 s f b x) = (term163 _128066 x s f b).
Proof. exact (eq_refl (term173 _128066 s f b x)). Qed.
Lemma lem6976592 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term174 _128066 s f b) = (term165 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976591 _128066 x s f b)). Qed.
Lemma lem6976593 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976594 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term175 _128066 s f b) = (term166 _128066 s f b).
Proof. exact (MK_COMB (@lem6976593 _128066) (@lem6976592 _128066 s f b)). Qed.
Lemma lem6976595 {_128066 : Type'} (s : _128066 -> Prop) : (term136 _128066 s) = (term136 _128066 s).
Proof. exact (eq_refl (term136 _128066 s)). Qed.
Lemma lem6976596 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term170 _128066 s f b) = (term167 _128066 s f b).
Proof. exact (MK_COMB (@lem6976595 _128066 s) (@lem6976594 _128066 s f b)). Qed.
Lemma lem6976597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976598 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term176 _128066 s f b) = (term177 _128066 s f b).
Proof. exact (MK_COMB (@lem6976597) (@lem6976596 _128066 s f b)). Qed.
Lemma lem6976599 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term173 _128066 s f b x) = (term163 _128066 x s f b).
Proof. exact (eq_refl (term173 _128066 s f b x)). Qed.
Lemma lem6976600 {_128066 : Type'} (s : _128066 -> Prop) : (term136 _128066 s) = (term136 _128066 s).
Proof. exact (eq_refl (term136 _128066 s)). Qed.
Lemma lem6976601 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term178 _128066 s f b x) = (term179 _128066 x s f b).
Proof. exact (MK_COMB (@lem6976600 _128066 s) (@lem6976599 _128066 x s f b)). Qed.
Lemma lem6976602 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term180 _128066 s f b) = (term181 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976601 _128066 x s f b)). Qed.
Lemma lem6976603 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976604 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term171 _128066 s f b) = (term182 _128066 s f b).
Proof. exact (MK_COMB (@lem6976603 _128066) (@lem6976602 _128066 s f b)). Qed.
Lemma lem6976605 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : ((term170 _128066 s f b) = (term171 _128066 s f b)) = ((term167 _128066 s f b) = (term182 _128066 s f b)).
Proof. exact (MK_COMB (@lem6976598 _128066 s f b) (@lem6976604 _128066 s f b)). Qed.
Lemma lem6976606 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term167 _128066 s f b) = (term182 _128066 s f b).
Proof. exact (EQ_MP (@lem6976605 _128066 s f b) (@lem6976590 _128066 s f b)). Qed.
Lemma lem6976607 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term138 _128066 s f b) = (term182 _128066 s f b).
Proof. exact (TRANS (@lem6976586 _128066 s f b) (@lem6976606 _128066 s f b)). Qed.
Lemma lem6976608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976609 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term141 _128066 s f b) = (term183 _128066 s f b).
Proof. exact (MK_COMB (@lem6976608) (@lem6976607 _128066 s f b)). Qed.
Lemma lem6976610 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6976611 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term143 _128066 f s b) = (term184 _128066 f s b).
Proof. exact (MK_COMB (@lem6976609 _128066 s f b) (@lem6976610 _128066 f s b)). Qed.
Lemma lem6976613 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6976614 {_128066 : Type'} (P : _128066 -> Prop) (Q : Prop) : (term150 _128066 P Q) = (term151 _128066 P Q).
Proof. exact (@lem6976613 _128066 P Q). Qed.
Lemma lem6976615 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term185 _128066 f s b) = (term186 _128066 f s b).
Proof. exact (@lem6976614 _128066 (term181 _128066 s f b) (term39 _128066 f s b)). Qed.
Lemma lem6976616 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term187 _128066 s f b x) = (term179 _128066 x s f b).
Proof. exact (eq_refl (term187 _128066 s f b x)). Qed.
Lemma lem6976617 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term188 _128066 s f b) = (term181 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976616 _128066 x s f b)). Qed.
Lemma lem6976618 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976619 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term189 _128066 s f b) = (term182 _128066 s f b).
Proof. exact (MK_COMB (@lem6976618 _128066) (@lem6976617 _128066 s f b)). Qed.
Lemma lem6976620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976621 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term190 _128066 s f b) = (term183 _128066 s f b).
Proof. exact (MK_COMB (@lem6976620) (@lem6976619 _128066 s f b)). Qed.
Lemma lem6976622 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6976623 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term185 _128066 f s b) = (term184 _128066 f s b).
Proof. exact (MK_COMB (@lem6976621 _128066 s f b) (@lem6976622 _128066 f s b)). Qed.
Lemma lem6976624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976625 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term191 _128066 f s b) = (term192 _128066 f s b).
Proof. exact (MK_COMB (@lem6976624) (@lem6976623 _128066 f s b)). Qed.
Lemma lem6976626 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term187 _128066 s f b x) = (term179 _128066 x s f b).
Proof. exact (eq_refl (term187 _128066 s f b x)). Qed.
Lemma lem6976627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976628 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term193 _128066 s f b x) = (term194 _128066 x s f b).
Proof. exact (MK_COMB (@lem6976627) (@lem6976626 _128066 x s f b)). Qed.
Lemma lem6976629 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term39 _128066 f s b).
Proof. exact (eq_refl (term39 _128066 f s b)). Qed.
Lemma lem6976630 {_128066 : Type'} (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term195 _128066 x f s b) = (term196 _128066 x f s b).
Proof. exact (MK_COMB (@lem6976628 _128066 x s f b) (@lem6976629 _128066 f s b)). Qed.
Lemma lem6976631 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term197 _128066 f s b) = (term198 _128066 f s b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976630 _128066 x f s b)). Qed.
Lemma lem6976632 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976633 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term186 _128066 f s b) = (term199 _128066 f s b).
Proof. exact (MK_COMB (@lem6976632 _128066) (@lem6976631 _128066 f s b)). Qed.
Lemma lem6976634 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : ((term185 _128066 f s b) = (term186 _128066 f s b)) = ((term184 _128066 f s b) = (term199 _128066 f s b)).
Proof. exact (MK_COMB (@lem6976625 _128066 f s b) (@lem6976633 _128066 f s b)). Qed.
Lemma lem6976635 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term184 _128066 f s b) = (term199 _128066 f s b).
Proof. exact (EQ_MP (@lem6976634 _128066 f s b) (@lem6976615 _128066 f s b)). Qed.
Lemma lem6976636 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term143 _128066 f s b) = (term199 _128066 f s b).
Proof. exact (TRANS (@lem6976611 _128066 f s b) (@lem6976635 _128066 f s b)). Qed.
Lemma lem6976637 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term144 _128066 f s) = (term200 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6976636 _128066 f s b)). Qed.
Lemma lem6976638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976639 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term145 _128066 f s) = (term201 _128066 f s).
Proof. exact (MK_COMB (@lem6976638) (@lem6976637 _128066 f s)). Qed.
Lemma lem6976641 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6976642 {_128066 : Type'} (P : type1597 _128066) : (term204 _128066 P) = (term205 _128066 P).
Proof. exact (@lem6976641 nat _128066 P). Qed.
Lemma lem6976643 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term206 _128066 f s) = (term207 _128066 f s).
Proof. exact (@lem6976642 _128066 (term208 _128066 f s)). Qed.
Lemma lem6976644 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term209 _128066 f s b) = (term198 _128066 f s b).
Proof. exact (eq_refl (term209 _128066 f s b)). Qed.
Lemma lem6976645 {_128066 : Type'} (x : _128066) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6976646 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (x : _128066) : (term210 _128066 f s b x) = (term211 _128066 f s b x).
Proof. exact (MK_COMB (@lem6976644 _128066 f s b) (@lem6976645 _128066 x)). Qed.
Lemma lem6976647 {_128066 : Type'} (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term211 _128066 f s b x) = (term196 _128066 x f s b).
Proof. exact (eq_refl (term211 _128066 f s b x)). Qed.
Lemma lem6976648 {_128066 : Type'} (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term210 _128066 f s b x) = (term196 _128066 x f s b).
Proof. exact (TRANS (@lem6976646 _128066 f s b x) (@lem6976647 _128066 x f s b)). Qed.
Lemma lem6976649 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term212 _128066 f s b) = (term198 _128066 f s b).
Proof. exact (fun_ext (fun x : _128066 => @lem6976648 _128066 x f s b)). Qed.
Lemma lem6976650 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6976651 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term213 _128066 f s b) = (term199 _128066 f s b).
Proof. exact (MK_COMB (@lem6976650 _128066) (@lem6976649 _128066 f s b)). Qed.
Lemma lem6976652 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term214 _128066 f s) = (term200 _128066 f s).
Proof. exact (fun_ext (fun b : nat => @lem6976651 _128066 f s b)). Qed.
Lemma lem6976653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976654 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term206 _128066 f s) = (term201 _128066 f s).
Proof. exact (MK_COMB (@lem6976653) (@lem6976652 _128066 f s)). Qed.
Lemma lem6976655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976656 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term215 _128066 f s) = (term216 _128066 f s).
Proof. exact (MK_COMB (@lem6976655) (@lem6976654 _128066 f s)). Qed.
Lemma lem6976657 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term209 _128066 f s b) = (term198 _128066 f s b).
Proof. exact (eq_refl (term209 _128066 f s b)). Qed.
Lemma lem6976658 {_128066 : Type'} (x : nat -> _128066) (b : nat) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem6976659 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (x : nat -> _128066) (b : nat) : (term217 _128066 f s x b) = (term218 _128066 f s x b).
Proof. exact (MK_COMB (@lem6976657 _128066 f s b) (@lem6976658 _128066 x b)). Qed.
Lemma lem6976660 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term218 _128066 f s x b) = (term219 _128066 x f s b).
Proof. exact (eq_refl (term218 _128066 f s x b)). Qed.
Lemma lem6976661 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term217 _128066 f s x b) = (term219 _128066 x f s b).
Proof. exact (TRANS (@lem6976659 _128066 f s x b) (@lem6976660 _128066 x f s b)). Qed.
Lemma lem6976662 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term220 _128066 f s x) = (term221 _128066 x f s).
Proof. exact (fun_ext (fun b : nat => @lem6976661 _128066 x f s b)). Qed.
Lemma lem6976663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976664 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term222 _128066 f s x) = (term223 _128066 x f s).
Proof. exact (MK_COMB (@lem6976663) (@lem6976662 _128066 x f s)). Qed.
Lemma lem6976665 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term224 _128066 f s) = (term225 _128066 f s).
Proof. exact (fun_ext (fun x : nat -> _128066 => @lem6976664 _128066 x f s)). Qed.
Lemma lem6976666 {_128066 : Type'} : (@ex (nat -> _128066)) = (@ex (nat -> _128066)).
Proof. exact (eq_refl (@ex (nat -> _128066))). Qed.
Lemma lem6976667 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term207 _128066 f s) = (term226 _128066 f s).
Proof. exact (MK_COMB (@lem6976666 _128066) (@lem6976665 _128066 f s)). Qed.
Lemma lem6976668 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : ((term206 _128066 f s) = (term207 _128066 f s)) = ((term201 _128066 f s) = (term226 _128066 f s)).
Proof. exact (MK_COMB (@lem6976656 _128066 f s) (@lem6976667 _128066 f s)). Qed.
Lemma lem6976669 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term201 _128066 f s) = (term226 _128066 f s).
Proof. exact (EQ_MP (@lem6976668 _128066 f s) (@lem6976643 _128066 f s)). Qed.
Lemma lem6976670 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term145 _128066 f s) = (term226 _128066 f s).
Proof. exact (TRANS (@lem6976639 _128066 f s) (@lem6976669 _128066 f s)). Qed.
Lemma lem6976671 {_128066 : Type'} (s : _128066 -> Prop) : (term146 _128066 s) = (term227 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976670 _128066 f s)). Qed.
Lemma lem6976672 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6976673 {_128066 : Type'} (s : _128066 -> Prop) : (term147 _128066 s) = (term228 _128066 s).
Proof. exact (MK_COMB (@lem6976672 _128066) (@lem6976671 _128066 s)). Qed.
Lemma lem6976675 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6976676 {_128066 : Type'} (P : type697 _128066) : (term229 _128066 P) = (term230 _128066 P).
Proof. exact (@lem6976675 (_128066 -> nat) (nat -> _128066) P). Qed.
Lemma lem6976677 {_128066 : Type'} (s : _128066 -> Prop) : (term231 _128066 s) = (term232 _128066 s).
Proof. exact (@lem6976676 _128066 (term233 _128066 s)). Qed.
Lemma lem6976678 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term234 _128066 s f) = (term225 _128066 f s).
Proof. exact (eq_refl (term234 _128066 s f)). Qed.
Lemma lem6976679 {_128066 : Type'} (x : nat -> _128066) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6976680 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (x : nat -> _128066) : (term235 _128066 s f x) = (term236 _128066 f s x).
Proof. exact (MK_COMB (@lem6976678 _128066 f s) (@lem6976679 _128066 x)). Qed.
Lemma lem6976681 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term236 _128066 f s x) = (term223 _128066 x f s).
Proof. exact (eq_refl (term236 _128066 f s x)). Qed.
Lemma lem6976682 {_128066 : Type'} (x : nat -> _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term235 _128066 s f x) = (term223 _128066 x f s).
Proof. exact (TRANS (@lem6976680 _128066 f s x) (@lem6976681 _128066 x f s)). Qed.
Lemma lem6976683 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term237 _128066 s f) = (term225 _128066 f s).
Proof. exact (fun_ext (fun x : nat -> _128066 => @lem6976682 _128066 x f s)). Qed.
Lemma lem6976684 {_128066 : Type'} : (@ex (nat -> _128066)) = (@ex (nat -> _128066)).
Proof. exact (eq_refl (@ex (nat -> _128066))). Qed.
Lemma lem6976685 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term238 _128066 s f) = (term226 _128066 f s).
Proof. exact (MK_COMB (@lem6976684 _128066) (@lem6976683 _128066 f s)). Qed.
Lemma lem6976686 {_128066 : Type'} (s : _128066 -> Prop) : (term239 _128066 s) = (term227 _128066 s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976685 _128066 f s)). Qed.
Lemma lem6976687 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6976688 {_128066 : Type'} (s : _128066 -> Prop) : (term231 _128066 s) = (term228 _128066 s).
Proof. exact (MK_COMB (@lem6976687 _128066) (@lem6976686 _128066 s)). Qed.
Lemma lem6976689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976690 {_128066 : Type'} (s : _128066 -> Prop) : (term240 _128066 s) = (term241 _128066 s).
Proof. exact (MK_COMB (@lem6976689) (@lem6976688 _128066 s)). Qed.
Lemma lem6976691 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) : (term234 _128066 s f) = (term225 _128066 f s).
Proof. exact (eq_refl (term234 _128066 s f)). Qed.
Lemma lem6976692 {_128066 : Type'} (x : type702 _128066) (f : _128066 -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6976693 {_128066 : Type'} (s : _128066 -> Prop) (x : type702 _128066) (f : _128066 -> nat) : (term242 _128066 s x f) = (term243 _128066 s x f).
Proof. exact (MK_COMB (@lem6976691 _128066 f s) (@lem6976692 _128066 x f)). Qed.
Lemma lem6976694 {_128066 : Type'} (x : type702 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term243 _128066 s x f) = (term244 _128066 x f s).
Proof. exact (eq_refl (term243 _128066 s x f)). Qed.
Lemma lem6976695 {_128066 : Type'} (x : type702 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term242 _128066 s x f) = (term244 _128066 x f s).
Proof. exact (TRANS (@lem6976693 _128066 s x f) (@lem6976694 _128066 x f s)). Qed.
Lemma lem6976696 {_128066 : Type'} (x : type702 _128066) (s : _128066 -> Prop) : (term245 _128066 s x) = (term246 _128066 x s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6976695 _128066 x f s)). Qed.
Lemma lem6976697 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6976698 {_128066 : Type'} (x : type702 _128066) (s : _128066 -> Prop) : (term247 _128066 s x) = (term248 _128066 x s).
Proof. exact (MK_COMB (@lem6976697 _128066) (@lem6976696 _128066 x s)). Qed.
Lemma lem6976699 {_128066 : Type'} (s : _128066 -> Prop) : (term249 _128066 s) = (term250 _128066 s).
Proof. exact (fun_ext (fun x : type702 _128066 => @lem6976698 _128066 x s)). Qed.
Lemma lem6976700 {_128066 : Type'} : (@ex ((_128066 -> nat) -> nat -> _128066)) = (@ex ((_128066 -> nat) -> nat -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> nat) -> nat -> _128066))). Qed.
Lemma lem6976701 {_128066 : Type'} (s : _128066 -> Prop) : (term232 _128066 s) = (term251 _128066 s).
Proof. exact (MK_COMB (@lem6976700 _128066) (@lem6976699 _128066 s)). Qed.
Lemma lem6976702 {_128066 : Type'} (s : _128066 -> Prop) : ((term231 _128066 s) = (term232 _128066 s)) = ((term228 _128066 s) = (term251 _128066 s)).
Proof. exact (MK_COMB (@lem6976690 _128066 s) (@lem6976701 _128066 s)). Qed.
Lemma lem6976703 {_128066 : Type'} (s : _128066 -> Prop) : (term228 _128066 s) = (term251 _128066 s).
Proof. exact (EQ_MP (@lem6976702 _128066 s) (@lem6976677 _128066 s)). Qed.
Lemma lem6976704 {_128066 : Type'} (s : _128066 -> Prop) : (term147 _128066 s) = (term251 _128066 s).
Proof. exact (TRANS (@lem6976673 _128066 s) (@lem6976703 _128066 s)). Qed.
Lemma lem6976705 {_128066 : Type'} : (term148 _128066) = (term252 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976704 _128066 s)). Qed.
Lemma lem6976706 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6976707 {_128066 : Type'} : (term149 _128066) = (term253 _128066).
Proof. exact (MK_COMB (@lem6976706 _128066) (@lem6976705 _128066)). Qed.
Lemma lem6976709 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6976710 {_128066 : Type'} (P : type601 _128066) : (term254 _128066 P) = (term255 _128066 P).
Proof. exact (@lem6976709 (_128066 -> Prop) (type702 _128066) P). Qed.
Lemma lem6976711 {_128066 : Type'} : (term256 _128066) = (term257 _128066).
Proof. exact (@lem6976710 _128066 (term258 _128066)). Qed.
Lemma lem6976712 {_128066 : Type'} (s : _128066 -> Prop) : (term259 _128066 s) = (term250 _128066 s).
Proof. exact (eq_refl (term259 _128066 s)). Qed.
Lemma lem6976713 {_128066 : Type'} (x : type702 _128066) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6976714 {_128066 : Type'} (s : _128066 -> Prop) (x : type702 _128066) : (term260 _128066 s x) = (term261 _128066 s x).
Proof. exact (MK_COMB (@lem6976712 _128066 s) (@lem6976713 _128066 x)). Qed.
Lemma lem6976715 {_128066 : Type'} (x : type702 _128066) (s : _128066 -> Prop) : (term261 _128066 s x) = (term248 _128066 x s).
Proof. exact (eq_refl (term261 _128066 s x)). Qed.
Lemma lem6976716 {_128066 : Type'} (x : type702 _128066) (s : _128066 -> Prop) : (term260 _128066 s x) = (term248 _128066 x s).
Proof. exact (TRANS (@lem6976714 _128066 s x) (@lem6976715 _128066 x s)). Qed.
Lemma lem6976717 {_128066 : Type'} (s : _128066 -> Prop) : (term262 _128066 s) = (term250 _128066 s).
Proof. exact (fun_ext (fun x : type702 _128066 => @lem6976716 _128066 x s)). Qed.
Lemma lem6976718 {_128066 : Type'} : (@ex ((_128066 -> nat) -> nat -> _128066)) = (@ex ((_128066 -> nat) -> nat -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> nat) -> nat -> _128066))). Qed.
Lemma lem6976719 {_128066 : Type'} (s : _128066 -> Prop) : (term263 _128066 s) = (term251 _128066 s).
Proof. exact (MK_COMB (@lem6976718 _128066) (@lem6976717 _128066 s)). Qed.
Lemma lem6976720 {_128066 : Type'} : (term264 _128066) = (term252 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976719 _128066 s)). Qed.
Lemma lem6976721 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6976722 {_128066 : Type'} : (term256 _128066) = (term253 _128066).
Proof. exact (MK_COMB (@lem6976721 _128066) (@lem6976720 _128066)). Qed.
Lemma lem6976723 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976724 {_128066 : Type'} : (term265 _128066) = (term266 _128066).
Proof. exact (MK_COMB (@lem6976723) (@lem6976722 _128066)). Qed.
Lemma lem6976725 {_128066 : Type'} (s : _128066 -> Prop) : (term259 _128066 s) = (term250 _128066 s).
Proof. exact (eq_refl (term259 _128066 s)). Qed.
Lemma lem6976726 {_128066 : Type'} (x : type642 _128066) (s : _128066 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6976727 {_128066 : Type'} (x : type642 _128066) (s : _128066 -> Prop) : (term267 _128066 x s) = (term268 _128066 x s).
Proof. exact (MK_COMB (@lem6976725 _128066 s) (@lem6976726 _128066 x s)). Qed.
Lemma lem6976728 {_128066 : Type'} (x : type642 _128066) (s : _128066 -> Prop) : (term268 _128066 x s) = (term269 _128066 x s).
Proof. exact (eq_refl (term268 _128066 x s)). Qed.
Lemma lem6976729 {_128066 : Type'} (x : type642 _128066) (s : _128066 -> Prop) : (term267 _128066 x s) = (term269 _128066 x s).
Proof. exact (TRANS (@lem6976727 _128066 x s) (@lem6976728 _128066 x s)). Qed.
Lemma lem6976730 {_128066 : Type'} (x : type642 _128066) : (term270 _128066 x) = (term271 _128066 x).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6976729 _128066 x s)). Qed.
Lemma lem6976731 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6976732 {_128066 : Type'} (x : type642 _128066) : (term272 _128066 x) = (term273 _128066 x).
Proof. exact (MK_COMB (@lem6976731 _128066) (@lem6976730 _128066 x)). Qed.
Lemma lem6976733 {_128066 : Type'} : (term274 _128066) = (term275 _128066).
Proof. exact (fun_ext (fun x : type642 _128066 => @lem6976732 _128066 x)). Qed.
Lemma lem6976734 {_128066 : Type'} : (@ex ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066)) = (@ex ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066))). Qed.
Lemma lem6976735 {_128066 : Type'} : (term257 _128066) = (term276 _128066).
Proof. exact (MK_COMB (@lem6976734 _128066) (@lem6976733 _128066)). Qed.
Lemma lem6976736 {_128066 : Type'} : ((term256 _128066) = (term257 _128066)) = ((term253 _128066) = (term276 _128066)).
Proof. exact (MK_COMB (@lem6976724 _128066) (@lem6976735 _128066)). Qed.
Lemma lem6976737 {_128066 : Type'} : (term253 _128066) = (term276 _128066).
Proof. exact (EQ_MP (@lem6976736 _128066) (@lem6976711 _128066)). Qed.
Lemma lem6976739 {_128066 : Type'} : (term149 _128066) = (term276 _128066).
Proof. exact (TRANS (@lem6976707 _128066) (@lem6976737 _128066)). Qed.
Lemma lem6976740 {_128066 : Type'} : (term12 _128066) = (term276 _128066).
Proof. exact (TRANS (@lem6976407 _128066) (@lem6976739 _128066)). Qed.
Lemma lem6976741 {_128066 : Type'} (h1 : term12 _128066) : term276 _128066.
Proof. exact (EQ_MP (@lem6976740 _128066) (@lem6976181 _128066 h1)). Qed.
Lemma lem6976749 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term108 A s f x b) = (term109 A s f x b).
Proof. exact (@lem17362 (@IN A x s) (term110 A f x b)). Qed.
Lemma lem6976750 {A : Type'} (P : A -> Prop) : (term111 A P) = (term112 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem6976751 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term113 A s f b) = (term114 A s f b).
Proof. exact (@lem6976750 A (term44 A s f b)). Qed.
Lemma lem6976752 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term115 A s f b x) = (term43 A s f x b).
Proof. exact (eq_refl (term115 A s f b x)). Qed.
Lemma lem6976753 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976754 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term116 A s f b x) = (term108 A s f x b).
Proof. exact (MK_COMB (@lem6976753) (@lem6976752 A s f x b)). Qed.
Lemma lem6976755 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term116 A s f b x) = (term109 A s f x b).
Proof. exact (TRANS (@lem6976754 A s f x b) (@lem6976749 A s f x b)). Qed.
Lemma lem6976756 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term117 A s f b) = (term118 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976755 A s f x b)). Qed.
Lemma lem6976757 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6976758 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term114 A s f b) = (term119 A s f b).
Proof. exact (MK_COMB (@lem6976757 A) (@lem6976756 A s f b)). Qed.
Lemma lem6976759 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term113 A s f b) = (term119 A s f b).
Proof. exact (TRANS (@lem6976751 A s f b) (@lem6976758 A s f b)). Qed.
Lemma lem6976766 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term120 A s f x b) = (term121 A s f x b).
Proof. exact (@lem17045 (@IN A x s) (term71 A f x b)). Qed.
Lemma lem6976767 {A : Type'} (P : A -> Prop) : (term122 A P) = (term123 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem6976768 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term124 A s f b) = (term125 A s f b).
Proof. exact (@lem6976767 A (term41 A s f b)). Qed.
Lemma lem6976769 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term126 A s f b x) = (term40 A s f x b).
Proof. exact (eq_refl (term126 A s f b x)). Qed.
Lemma lem6976770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6976771 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term127 A s f b x) = (term120 A s f x b).
Proof. exact (MK_COMB (@lem6976770) (@lem6976769 A s f x b)). Qed.
Lemma lem6976772 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term127 A s f b x) = (term121 A s f x b).
Proof. exact (TRANS (@lem6976771 A s f x b) (@lem6976766 A s f x b)). Qed.
Lemma lem6976773 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term128 A s f b) = (term129 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976772 A s f x b)). Qed.
Lemma lem6976774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6976775 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term125 A s f b) = (term130 A s f b).
Proof. exact (MK_COMB (@lem6976774 A) (@lem6976773 A s f b)). Qed.
Lemma lem6976776 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term124 A s f b) = (term130 A s f b).
Proof. exact (TRANS (@lem6976768 A s f b) (@lem6976775 A s f b)). Qed.
Lemma lem6976777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976778 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term131 A s f b) = (term132 A s f b).
Proof. exact (MK_COMB (@lem6976777) (@lem6976759 A s f b)). Qed.
Lemma lem6976779 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term133 A s f b) = (term134 A s f b).
Proof. exact (MK_COMB (@lem6976778 A s f b) (@lem6976776 A s f b)). Qed.
Lemma lem6976780 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term135 A s f b) = (term133 A s f b).
Proof. exact (@lem17045 (term45 A s f b) (term42 A s f b)). Qed.
Lemma lem6976781 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term135 A s f b) = (term134 A s f b).
Proof. exact (TRANS (@lem6976780 A s f b) (@lem6976779 A s f b)). Qed.
Lemma lem6976783 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem6976784 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term137 A s f b) = (term138 A s f b).
Proof. exact (MK_COMB (@lem6976783 A s) (@lem6976781 A s f b)). Qed.
Lemma lem6976785 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term139 A s f b) = (term137 A s f b).
Proof. exact (@lem17045 (@FINITE A s) (term47 A s f b)). Qed.
Lemma lem6976786 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term139 A s f b) = (term138 A s f b).
Proof. exact (TRANS (@lem6976785 A s f b) (@lem6976784 A s f b)). Qed.
Lemma lem6976787 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem6976788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976789 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term140 A s f b) = (term141 A s f b).
Proof. exact (MK_COMB (@lem6976788) (@lem6976786 A s f b)). Qed.
Lemma lem6976790 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term142 A f s b) = (term143 A f s b).
Proof. exact (MK_COMB (@lem6976789 A s f b) (@lem6976787 A f s b)). Qed.
Lemma lem6976791 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term51 A f s b) = (term142 A f s b).
Proof. exact (@lem17265 (term49 A s f b) (term39 A f s b)). Qed.
Lemma lem6976792 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term51 A f s b) = (term143 A f s b).
Proof. exact (TRANS (@lem6976791 A f s b) (@lem6976790 A f s b)). Qed.
Lemma lem6976793 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term52 A f s) = (term144 A f s).
Proof. exact (fun_ext (fun b : nat => @lem6976792 A f s b)). Qed.
Lemma lem6976794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6976795 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term53 A f s) = (term145 A f s).
Proof. exact (MK_COMB (@lem6976794) (@lem6976793 A f s)). Qed.
Lemma lem6976796 {A : Type'} (s : A -> Prop) : (term54 A s) = (term146 A s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6976795 A f s)). Qed.
Lemma lem6976797 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6976798 {A : Type'} (s : A -> Prop) : (term55 A s) = (term147 A s).
Proof. exact (MK_COMB (@lem6976797 A) (@lem6976796 A s)). Qed.
Lemma lem6976799 {A : Type'} : (term56 A) = (term148 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6976798 A s)). Qed.
Lemma lem6976800 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6976801 {A : Type'} : (term12 A) = (term149 A).
Proof. exact (MK_COMB (@lem6976800 A) (@lem6976799 A)). Qed.
Lemma lem6976956 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6976957 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (@lem6976956 A P Q). Qed.
Lemma lem6976958 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term152 A s f b) = (term153 A s f b).
Proof. exact (@lem6976957 A (term118 A s f b) (term130 A s f b)). Qed.
Lemma lem6976959 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term154 A s f b x) = (term109 A s f x b).
Proof. exact (eq_refl (term154 A s f b x)). Qed.
Lemma lem6976960 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term155 A s f b) = (term118 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976959 A s f x b)). Qed.
Lemma lem6976961 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6976962 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term156 A s f b) = (term119 A s f b).
Proof. exact (MK_COMB (@lem6976961 A) (@lem6976960 A s f b)). Qed.
Lemma lem6976963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976964 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term157 A s f b) = (term132 A s f b).
Proof. exact (MK_COMB (@lem6976963) (@lem6976962 A s f b)). Qed.
Lemma lem6976965 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term130 A s f b) = (term130 A s f b).
Proof. exact (eq_refl (term130 A s f b)). Qed.
Lemma lem6976966 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term152 A s f b) = (term134 A s f b).
Proof. exact (MK_COMB (@lem6976964 A s f b) (@lem6976965 A s f b)). Qed.
Lemma lem6976967 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976968 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term158 A s f b) = (term159 A s f b).
Proof. exact (MK_COMB (@lem6976967) (@lem6976966 A s f b)). Qed.
Lemma lem6976969 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term154 A s f b x) = (term109 A s f x b).
Proof. exact (eq_refl (term154 A s f b x)). Qed.
Lemma lem6976970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6976971 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term160 A s f b x) = (term161 A s f x b).
Proof. exact (MK_COMB (@lem6976970) (@lem6976969 A s f x b)). Qed.
Lemma lem6976972 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term130 A s f b) = (term130 A s f b).
Proof. exact (eq_refl (term130 A s f b)). Qed.
Lemma lem6976973 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term162 A x s f b) = (term163 A x s f b).
Proof. exact (MK_COMB (@lem6976971 A s f x b) (@lem6976972 A s f b)). Qed.
Lemma lem6976974 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term164 A s f b) = (term165 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976973 A x s f b)). Qed.
Lemma lem6976975 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6976976 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term153 A s f b) = (term166 A s f b).
Proof. exact (MK_COMB (@lem6976975 A) (@lem6976974 A s f b)). Qed.
Lemma lem6976977 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : ((term152 A s f b) = (term153 A s f b)) = ((term134 A s f b) = (term166 A s f b)).
Proof. exact (MK_COMB (@lem6976968 A s f b) (@lem6976976 A s f b)). Qed.
Lemma lem6976978 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term134 A s f b) = (term166 A s f b).
Proof. exact (EQ_MP (@lem6976977 A s f b) (@lem6976958 A s f b)). Qed.
Lemma lem6976979 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem6976980 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term138 A s f b) = (term167 A s f b).
Proof. exact (MK_COMB (@lem6976979 A s) (@lem6976978 A s f b)). Qed.
Lemma lem6976982 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6976983 {A : Type'} (P : Prop) (Q : A -> Prop) : (term168 A P Q) = (term169 A P Q).
Proof. exact (@lem6976982 A P Q). Qed.
Lemma lem6976984 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term170 A s f b) = (term171 A s f b).
Proof. exact (@lem6976983 A (term172 A s) (term165 A s f b)). Qed.
Lemma lem6976985 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term173 A s f b x) = (term163 A x s f b).
Proof. exact (eq_refl (term173 A s f b x)). Qed.
Lemma lem6976986 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term174 A s f b) = (term165 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976985 A x s f b)). Qed.
Lemma lem6976987 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6976988 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term175 A s f b) = (term166 A s f b).
Proof. exact (MK_COMB (@lem6976987 A) (@lem6976986 A s f b)). Qed.
Lemma lem6976989 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem6976990 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term170 A s f b) = (term167 A s f b).
Proof. exact (MK_COMB (@lem6976989 A s) (@lem6976988 A s f b)). Qed.
Lemma lem6976991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6976992 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term176 A s f b) = (term177 A s f b).
Proof. exact (MK_COMB (@lem6976991) (@lem6976990 A s f b)). Qed.
Lemma lem6976993 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term173 A s f b x) = (term163 A x s f b).
Proof. exact (eq_refl (term173 A s f b x)). Qed.
Lemma lem6976994 {A : Type'} (s : A -> Prop) : (term136 A s) = (term136 A s).
Proof. exact (eq_refl (term136 A s)). Qed.
Lemma lem6976995 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term178 A s f b x) = (term179 A x s f b).
Proof. exact (MK_COMB (@lem6976994 A s) (@lem6976993 A x s f b)). Qed.
Lemma lem6976996 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term180 A s f b) = (term181 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6976995 A x s f b)). Qed.
Lemma lem6976997 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6976998 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term171 A s f b) = (term182 A s f b).
Proof. exact (MK_COMB (@lem6976997 A) (@lem6976996 A s f b)). Qed.
Lemma lem6976999 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : ((term170 A s f b) = (term171 A s f b)) = ((term167 A s f b) = (term182 A s f b)).
Proof. exact (MK_COMB (@lem6976992 A s f b) (@lem6976998 A s f b)). Qed.
Lemma lem6977000 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term167 A s f b) = (term182 A s f b).
Proof. exact (EQ_MP (@lem6976999 A s f b) (@lem6976984 A s f b)). Qed.
Lemma lem6977001 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term138 A s f b) = (term182 A s f b).
Proof. exact (TRANS (@lem6976980 A s f b) (@lem6977000 A s f b)). Qed.
Lemma lem6977002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977003 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term141 A s f b) = (term183 A s f b).
Proof. exact (MK_COMB (@lem6977002) (@lem6977001 A s f b)). Qed.
Lemma lem6977004 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem6977005 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term143 A f s b) = (term184 A f s b).
Proof. exact (MK_COMB (@lem6977003 A s f b) (@lem6977004 A f s b)). Qed.
Lemma lem6977007 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6977008 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (@lem6977007 A P Q). Qed.
Lemma lem6977009 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term185 A f s b) = (term186 A f s b).
Proof. exact (@lem6977008 A (term181 A s f b) (term39 A f s b)). Qed.
Lemma lem6977010 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term187 A s f b x) = (term179 A x s f b).
Proof. exact (eq_refl (term187 A s f b x)). Qed.
Lemma lem6977011 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term188 A s f b) = (term181 A s f b).
Proof. exact (fun_ext (fun x : A => @lem6977010 A x s f b)). Qed.
Lemma lem6977012 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6977013 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term189 A s f b) = (term182 A s f b).
Proof. exact (MK_COMB (@lem6977012 A) (@lem6977011 A s f b)). Qed.
Lemma lem6977014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977015 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term190 A s f b) = (term183 A s f b).
Proof. exact (MK_COMB (@lem6977014) (@lem6977013 A s f b)). Qed.
Lemma lem6977016 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem6977017 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term185 A f s b) = (term184 A f s b).
Proof. exact (MK_COMB (@lem6977015 A s f b) (@lem6977016 A f s b)). Qed.
Lemma lem6977018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977019 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term191 A f s b) = (term192 A f s b).
Proof. exact (MK_COMB (@lem6977018) (@lem6977017 A f s b)). Qed.
Lemma lem6977020 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term187 A s f b x) = (term179 A x s f b).
Proof. exact (eq_refl (term187 A s f b x)). Qed.
Lemma lem6977021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977022 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) : (term193 A s f b x) = (term194 A x s f b).
Proof. exact (MK_COMB (@lem6977021) (@lem6977020 A x s f b)). Qed.
Lemma lem6977023 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term39 A f s b) = (term39 A f s b).
Proof. exact (eq_refl (term39 A f s b)). Qed.
Lemma lem6977024 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (b : nat) : (term195 A x f s b) = (term196 A x f s b).
Proof. exact (MK_COMB (@lem6977022 A x s f b) (@lem6977023 A f s b)). Qed.
Lemma lem6977025 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term197 A f s b) = (term198 A f s b).
Proof. exact (fun_ext (fun x : A => @lem6977024 A x f s b)). Qed.
Lemma lem6977026 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6977027 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term186 A f s b) = (term199 A f s b).
Proof. exact (MK_COMB (@lem6977026 A) (@lem6977025 A f s b)). Qed.
Lemma lem6977028 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : ((term185 A f s b) = (term186 A f s b)) = ((term184 A f s b) = (term199 A f s b)).
Proof. exact (MK_COMB (@lem6977019 A f s b) (@lem6977027 A f s b)). Qed.
Lemma lem6977029 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term184 A f s b) = (term199 A f s b).
Proof. exact (EQ_MP (@lem6977028 A f s b) (@lem6977009 A f s b)). Qed.
Lemma lem6977030 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term143 A f s b) = (term199 A f s b).
Proof. exact (TRANS (@lem6977005 A f s b) (@lem6977029 A f s b)). Qed.
Lemma lem6977031 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term144 A f s) = (term200 A f s).
Proof. exact (fun_ext (fun b : nat => @lem6977030 A f s b)). Qed.
Lemma lem6977032 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977033 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term145 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem6977032) (@lem6977031 A f s)). Qed.
Lemma lem6977035 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6977036 {A : Type'} (P : type1597 A) : (term204 A P) = (term205 A P).
Proof. exact (@lem6977035 nat A P). Qed.
Lemma lem6977037 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term206 A f s) = (term207 A f s).
Proof. exact (@lem6977036 A (term208 A f s)). Qed.
Lemma lem6977038 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term209 A f s b) = (term198 A f s b).
Proof. exact (eq_refl (term209 A f s b)). Qed.
Lemma lem6977039 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6977040 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (x : A) : (term210 A f s b x) = (term211 A f s b x).
Proof. exact (MK_COMB (@lem6977038 A f s b) (@lem6977039 A x)). Qed.
Lemma lem6977041 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (b : nat) : (term211 A f s b x) = (term196 A x f s b).
Proof. exact (eq_refl (term211 A f s b x)). Qed.
Lemma lem6977042 {A : Type'} (x : A) (f : A -> nat) (s : A -> Prop) (b : nat) : (term210 A f s b x) = (term196 A x f s b).
Proof. exact (TRANS (@lem6977040 A f s b x) (@lem6977041 A x f s b)). Qed.
Lemma lem6977043 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term212 A f s b) = (term198 A f s b).
Proof. exact (fun_ext (fun x : A => @lem6977042 A x f s b)). Qed.
Lemma lem6977044 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem6977045 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term213 A f s b) = (term199 A f s b).
Proof. exact (MK_COMB (@lem6977044 A) (@lem6977043 A f s b)). Qed.
Lemma lem6977046 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term214 A f s) = (term200 A f s).
Proof. exact (fun_ext (fun b : nat => @lem6977045 A f s b)). Qed.
Lemma lem6977047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977048 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term206 A f s) = (term201 A f s).
Proof. exact (MK_COMB (@lem6977047) (@lem6977046 A f s)). Qed.
Lemma lem6977049 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977050 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term215 A f s) = (term216 A f s).
Proof. exact (MK_COMB (@lem6977049) (@lem6977048 A f s)). Qed.
Lemma lem6977051 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term209 A f s b) = (term198 A f s b).
Proof. exact (eq_refl (term209 A f s b)). Qed.
Lemma lem6977052 {A : Type'} (x : nat -> A) (b : nat) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem6977053 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : nat -> A) (b : nat) : (term217 A f s x b) = (term218 A f s x b).
Proof. exact (MK_COMB (@lem6977051 A f s b) (@lem6977052 A x b)). Qed.
Lemma lem6977054 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) (b : nat) : (term218 A f s x b) = (term219 A x f s b).
Proof. exact (eq_refl (term218 A f s x b)). Qed.
Lemma lem6977055 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) (b : nat) : (term217 A f s x b) = (term219 A x f s b).
Proof. exact (TRANS (@lem6977053 A f s x b) (@lem6977054 A x f s b)). Qed.
Lemma lem6977056 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) : (term220 A f s x) = (term221 A x f s).
Proof. exact (fun_ext (fun b : nat => @lem6977055 A x f s b)). Qed.
Lemma lem6977057 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977058 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) : (term222 A f s x) = (term223 A x f s).
Proof. exact (MK_COMB (@lem6977057) (@lem6977056 A x f s)). Qed.
Lemma lem6977059 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term224 A f s) = (term225 A f s).
Proof. exact (fun_ext (fun x : nat -> A => @lem6977058 A x f s)). Qed.
Lemma lem6977060 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem6977061 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term207 A f s) = (term226 A f s).
Proof. exact (MK_COMB (@lem6977060 A) (@lem6977059 A f s)). Qed.
Lemma lem6977062 {A : Type'} (f : A -> nat) (s : A -> Prop) : ((term206 A f s) = (term207 A f s)) = ((term201 A f s) = (term226 A f s)).
Proof. exact (MK_COMB (@lem6977050 A f s) (@lem6977061 A f s)). Qed.
Lemma lem6977063 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term201 A f s) = (term226 A f s).
Proof. exact (EQ_MP (@lem6977062 A f s) (@lem6977037 A f s)). Qed.
Lemma lem6977064 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term145 A f s) = (term226 A f s).
Proof. exact (TRANS (@lem6977033 A f s) (@lem6977063 A f s)). Qed.
Lemma lem6977065 {A : Type'} (s : A -> Prop) : (term146 A s) = (term227 A s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6977064 A f s)). Qed.
Lemma lem6977066 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6977067 {A : Type'} (s : A -> Prop) : (term147 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem6977066 A) (@lem6977065 A s)). Qed.
Lemma lem6977069 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6977070 {A : Type'} (P : type697 A) : (term229 A P) = (term230 A P).
Proof. exact (@lem6977069 (A -> nat) (nat -> A) P). Qed.
Lemma lem6977071 {A : Type'} (s : A -> Prop) : (term231 A s) = (term232 A s).
Proof. exact (@lem6977070 A (term233 A s)). Qed.
Lemma lem6977072 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term234 A s f) = (term225 A f s).
Proof. exact (eq_refl (term234 A s f)). Qed.
Lemma lem6977073 {A : Type'} (x : nat -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6977074 {A : Type'} (f : A -> nat) (s : A -> Prop) (x : nat -> A) : (term235 A s f x) = (term236 A f s x).
Proof. exact (MK_COMB (@lem6977072 A f s) (@lem6977073 A x)). Qed.
Lemma lem6977075 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) : (term236 A f s x) = (term223 A x f s).
Proof. exact (eq_refl (term236 A f s x)). Qed.
Lemma lem6977076 {A : Type'} (x : nat -> A) (f : A -> nat) (s : A -> Prop) : (term235 A s f x) = (term223 A x f s).
Proof. exact (TRANS (@lem6977074 A f s x) (@lem6977075 A x f s)). Qed.
Lemma lem6977077 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term237 A s f) = (term225 A f s).
Proof. exact (fun_ext (fun x : nat -> A => @lem6977076 A x f s)). Qed.
Lemma lem6977078 {A : Type'} : (@ex (nat -> A)) = (@ex (nat -> A)).
Proof. exact (eq_refl (@ex (nat -> A))). Qed.
Lemma lem6977079 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term238 A s f) = (term226 A f s).
Proof. exact (MK_COMB (@lem6977078 A) (@lem6977077 A f s)). Qed.
Lemma lem6977080 {A : Type'} (s : A -> Prop) : (term239 A s) = (term227 A s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6977079 A f s)). Qed.
Lemma lem6977081 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6977082 {A : Type'} (s : A -> Prop) : (term231 A s) = (term228 A s).
Proof. exact (MK_COMB (@lem6977081 A) (@lem6977080 A s)). Qed.
Lemma lem6977083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977084 {A : Type'} (s : A -> Prop) : (term240 A s) = (term241 A s).
Proof. exact (MK_COMB (@lem6977083) (@lem6977082 A s)). Qed.
Lemma lem6977085 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term234 A s f) = (term225 A f s).
Proof. exact (eq_refl (term234 A s f)). Qed.
Lemma lem6977086 {A : Type'} (x : type702 A) (f : A -> nat) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem6977087 {A : Type'} (s : A -> Prop) (x : type702 A) (f : A -> nat) : (term242 A s x f) = (term243 A s x f).
Proof. exact (MK_COMB (@lem6977085 A f s) (@lem6977086 A x f)). Qed.
Lemma lem6977088 {A : Type'} (x : type702 A) (f : A -> nat) (s : A -> Prop) : (term243 A s x f) = (term244 A x f s).
Proof. exact (eq_refl (term243 A s x f)). Qed.
Lemma lem6977089 {A : Type'} (x : type702 A) (f : A -> nat) (s : A -> Prop) : (term242 A s x f) = (term244 A x f s).
Proof. exact (TRANS (@lem6977087 A s x f) (@lem6977088 A x f s)). Qed.
Lemma lem6977090 {A : Type'} (x : type702 A) (s : A -> Prop) : (term245 A s x) = (term246 A x s).
Proof. exact (fun_ext (fun f : A -> nat => @lem6977089 A x f s)). Qed.
Lemma lem6977091 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6977092 {A : Type'} (x : type702 A) (s : A -> Prop) : (term247 A s x) = (term248 A x s).
Proof. exact (MK_COMB (@lem6977091 A) (@lem6977090 A x s)). Qed.
Lemma lem6977093 {A : Type'} (s : A -> Prop) : (term249 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : type702 A => @lem6977092 A x s)). Qed.
Lemma lem6977094 {A : Type'} : (@ex ((A -> nat) -> nat -> A)) = (@ex ((A -> nat) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> nat -> A))). Qed.
Lemma lem6977095 {A : Type'} (s : A -> Prop) : (term232 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem6977094 A) (@lem6977093 A s)). Qed.
Lemma lem6977096 {A : Type'} (s : A -> Prop) : ((term231 A s) = (term232 A s)) = ((term228 A s) = (term251 A s)).
Proof. exact (MK_COMB (@lem6977084 A s) (@lem6977095 A s)). Qed.
Lemma lem6977097 {A : Type'} (s : A -> Prop) : (term228 A s) = (term251 A s).
Proof. exact (EQ_MP (@lem6977096 A s) (@lem6977071 A s)). Qed.
Lemma lem6977098 {A : Type'} (s : A -> Prop) : (term147 A s) = (term251 A s).
Proof. exact (TRANS (@lem6977067 A s) (@lem6977097 A s)). Qed.
Lemma lem6977099 {A : Type'} : (term148 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6977098 A s)). Qed.
Lemma lem6977100 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6977101 {A : Type'} : (term149 A) = (term253 A).
Proof. exact (MK_COMB (@lem6977100 A) (@lem6977099 A)). Qed.
Lemma lem6977103 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6977104 {A : Type'} (P : type601 A) : (term254 A P) = (term255 A P).
Proof. exact (@lem6977103 (A -> Prop) (type702 A) P). Qed.
Lemma lem6977105 {A : Type'} : (term256 A) = (term257 A).
Proof. exact (@lem6977104 A (term258 A)). Qed.
Lemma lem6977106 {A : Type'} (s : A -> Prop) : (term259 A s) = (term250 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem6977107 {A : Type'} (x : type702 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6977108 {A : Type'} (s : A -> Prop) (x : type702 A) : (term260 A s x) = (term261 A s x).
Proof. exact (MK_COMB (@lem6977106 A s) (@lem6977107 A x)). Qed.
Lemma lem6977109 {A : Type'} (x : type702 A) (s : A -> Prop) : (term261 A s x) = (term248 A x s).
Proof. exact (eq_refl (term261 A s x)). Qed.
Lemma lem6977110 {A : Type'} (x : type702 A) (s : A -> Prop) : (term260 A s x) = (term248 A x s).
Proof. exact (TRANS (@lem6977108 A s x) (@lem6977109 A x s)). Qed.
Lemma lem6977111 {A : Type'} (s : A -> Prop) : (term262 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : type702 A => @lem6977110 A x s)). Qed.
Lemma lem6977112 {A : Type'} : (@ex ((A -> nat) -> nat -> A)) = (@ex ((A -> nat) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> nat) -> nat -> A))). Qed.
Lemma lem6977113 {A : Type'} (s : A -> Prop) : (term263 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem6977112 A) (@lem6977111 A s)). Qed.
Lemma lem6977114 {A : Type'} : (term264 A) = (term252 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6977113 A s)). Qed.
Lemma lem6977115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6977116 {A : Type'} : (term256 A) = (term253 A).
Proof. exact (MK_COMB (@lem6977115 A) (@lem6977114 A)). Qed.
Lemma lem6977117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977118 {A : Type'} : (term265 A) = (term266 A).
Proof. exact (MK_COMB (@lem6977117) (@lem6977116 A)). Qed.
Lemma lem6977119 {A : Type'} (s : A -> Prop) : (term259 A s) = (term250 A s).
Proof. exact (eq_refl (term259 A s)). Qed.
Lemma lem6977120 {A : Type'} (x : type642 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6977121 {A : Type'} (x : type642 A) (s : A -> Prop) : (term267 A x s) = (term268 A x s).
Proof. exact (MK_COMB (@lem6977119 A s) (@lem6977120 A x s)). Qed.
Lemma lem6977122 {A : Type'} (x : type642 A) (s : A -> Prop) : (term268 A x s) = (term269 A x s).
Proof. exact (eq_refl (term268 A x s)). Qed.
Lemma lem6977123 {A : Type'} (x : type642 A) (s : A -> Prop) : (term267 A x s) = (term269 A x s).
Proof. exact (TRANS (@lem6977121 A x s) (@lem6977122 A x s)). Qed.
Lemma lem6977124 {A : Type'} (x : type642 A) : (term270 A x) = (term271 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6977123 A x s)). Qed.
Lemma lem6977125 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6977126 {A : Type'} (x : type642 A) : (term272 A x) = (term273 A x).
Proof. exact (MK_COMB (@lem6977125 A) (@lem6977124 A x)). Qed.
Lemma lem6977127 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (fun_ext (fun x : type642 A => @lem6977126 A x)). Qed.
Lemma lem6977128 {A : Type'} : (@ex ((A -> Prop) -> (A -> nat) -> nat -> A)) = (@ex ((A -> Prop) -> (A -> nat) -> nat -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> nat) -> nat -> A))). Qed.
Lemma lem6977129 {A : Type'} : (term257 A) = (term276 A).
Proof. exact (MK_COMB (@lem6977128 A) (@lem6977127 A)). Qed.
Lemma lem6977130 {A : Type'} : ((term256 A) = (term257 A)) = ((term253 A) = (term276 A)).
Proof. exact (MK_COMB (@lem6977118 A) (@lem6977129 A)). Qed.
Lemma lem6977131 {A : Type'} : (term253 A) = (term276 A).
Proof. exact (EQ_MP (@lem6977130 A) (@lem6977105 A)). Qed.
Lemma lem6977133 {A : Type'} : (term149 A) = (term276 A).
Proof. exact (TRANS (@lem6977101 A) (@lem6977131 A)). Qed.
Lemma lem6977134 {A : Type'} : (term12 A) = (term276 A).
Proof. exact (TRANS (@lem6976801 A) (@lem6977133 A)). Qed.
Lemma lem6977135 {A : Type'} (h1 : term12 A) : term276 A.
Proof. exact (EQ_MP (@lem6977134 A) (@lem6976182 A h1)). Qed.
Lemma lem6977142 (m : nat) (n : nat) : (term34 m n) = (term277 m n).
Proof. exact (@lem17265 (Peano.lt m n) (Peano.le m n)). Qed.
Lemma lem6977143 (m : nat) : (term35 m) = (term278 m).
Proof. exact (fun_ext (fun n : nat => @lem6977142 m n)). Qed.
Lemma lem6977144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977145 (m : nat) : (term36 m) = (term279 m).
Proof. exact (MK_COMB (@lem6977144) (@lem6977143 m)). Qed.
Lemma lem6977146 : term37 = term280.
Proof. exact (fun_ext (fun m : nat => @lem6977145 m)). Qed.
Lemma lem6977147 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977204 : term38 = term281.
Proof. exact (MK_COMB (@lem6977147) (@lem6977146)). Qed.
Lemma lem6977205 (h1 : term38) : term281.
Proof. exact (EQ_MP (@lem6977204) (@lem6976183 h1)). Qed.
Lemma lem6977207 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (@IN _128066 x s).
Proof. exact (eq_refl (@IN _128066 x s)). Qed.
Lemma lem6977208 {_128066 : Type'} (P : _128066 -> Prop) : (term122 _128066 P) = (term123 _128066 P).
Proof. exact (@lem18394 _128066 P). Qed.
Lemma lem6977209 {_128066 : Type'} (s : _128066 -> Prop) : (term282 _128066 s) = (term283 _128066 s).
Proof. exact (@lem6977208 _128066 (term30 _128066 s)). Qed.
Lemma lem6977210 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term284 _128066 s x) = (@IN _128066 x s).
Proof. exact (eq_refl (term284 _128066 s x)). Qed.
Lemma lem6977211 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977213 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term285 _128066 s x) = (term286 _128066 x s).
Proof. exact (MK_COMB (@lem6977211) (@lem6977210 _128066 x s)). Qed.
Lemma lem6977214 {_128066 : Type'} (s : _128066 -> Prop) : (term287 _128066 s) = (term288 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977213 _128066 x s)). Qed.
Lemma lem6977215 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6977216 {_128066 : Type'} (s : _128066 -> Prop) : (term283 _128066 s) = (term289 _128066 s).
Proof. exact (MK_COMB (@lem6977215 _128066) (@lem6977214 _128066 s)). Qed.
Lemma lem6977217 {_128066 : Type'} (s : _128066 -> Prop) : (term282 _128066 s) = (term289 _128066 s).
Proof. exact (TRANS (@lem6977209 _128066 s) (@lem6977216 _128066 s)). Qed.
Lemma lem6977218 {_128066 : Type'} (s : _128066 -> Prop) : (term30 _128066 s) = (term30 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977207 _128066 x s)). Qed.
Lemma lem6977219 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6977220 {_128066 : Type'} (s : _128066 -> Prop) : (term31 _128066 s) = (term31 _128066 s).
Proof. exact (MK_COMB (@lem6977219 _128066) (@lem6977218 _128066 s)). Qed.
Lemma lem6977221 {_128066 : Type'} (s : _128066 -> Prop) : (term29 _128066 s) = (term29 _128066 s).
Proof. exact (eq_refl (term29 _128066 s)). Qed.
Lemma lem6977224 {_128066 : Type'} (s : _128066 -> Prop) : (term290 _128066 s) = (s = (@EMPTY _128066)).
Proof. exact (@lem16933 (s = (@EMPTY _128066))). Qed.
Lemma lem6977225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977226 {_128066 : Type'} (s : _128066 -> Prop) : (term291 _128066 s) = (term292 _128066 s).
Proof. exact (MK_COMB (@lem6977225) (@lem6977217 _128066 s)). Qed.
Lemma lem6977227 {_128066 : Type'} (s : _128066 -> Prop) : (term293 _128066 s) = (term294 _128066 s).
Proof. exact (MK_COMB (@lem6977226 _128066 s) (@lem6977221 _128066 s)). Qed.
Lemma lem6977228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977229 {_128066 : Type'} (s : _128066 -> Prop) : (term295 _128066 s) = (term295 _128066 s).
Proof. exact (MK_COMB (@lem6977228) (@lem6977220 _128066 s)). Qed.
Lemma lem6977230 {_128066 : Type'} (s : _128066 -> Prop) : (term296 _128066 s) = (term297 _128066 s).
Proof. exact (MK_COMB (@lem6977229 _128066 s) (@lem6977224 _128066 s)). Qed.
Lemma lem6977231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977232 {_128066 : Type'} (s : _128066 -> Prop) : (term298 _128066 s) = (term299 _128066 s).
Proof. exact (MK_COMB (@lem6977231) (@lem6977230 _128066 s)). Qed.
Lemma lem6977233 {_128066 : Type'} (s : _128066 -> Prop) : (term300 _128066 s) = (term301 _128066 s).
Proof. exact (MK_COMB (@lem6977232 _128066 s) (@lem6977227 _128066 s)). Qed.
Lemma lem6977234 {_128066 : Type'} (s : _128066 -> Prop) : ((term31 _128066 s) = (term29 _128066 s)) = (term300 _128066 s).
Proof. exact (@lem17784 (term31 _128066 s) (term29 _128066 s)). Qed.
Lemma lem6977235 {_128066 : Type'} (s : _128066 -> Prop) : ((term31 _128066 s) = (term29 _128066 s)) = (term301 _128066 s).
Proof. exact (TRANS (@lem6977234 _128066 s) (@lem6977233 _128066 s)). Qed.
Lemma lem6977236 {_128066 : Type'} : (term33 _128066) = (term302 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977235 _128066 s)). Qed.
Lemma lem6977237 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977238 {_128066 : Type'} : (term11 _128066) = (term303 _128066).
Proof. exact (MK_COMB (@lem6977237 _128066) (@lem6977236 _128066)). Qed.
Lemma lem6977240 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term304 A P Q) = (term305 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6977241 {_128066 : Type'} (P : type686 _128066) (Q : type686 _128066) : (term306 _128066 P Q) = (term307 _128066 P Q).
Proof. exact (@lem6977240 (_128066 -> Prop) P Q). Qed.
Lemma lem6977242 {_128066 : Type'} : (term308 _128066) = (term309 _128066).
Proof. exact (@lem6977241 _128066 (term310 _128066) (term311 _128066)). Qed.
Lemma lem6977243 {_128066 : Type'} (s : _128066 -> Prop) : (term312 _128066 s) = (term297 _128066 s).
Proof. exact (eq_refl (term312 _128066 s)). Qed.
Lemma lem6977244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977245 {_128066 : Type'} (s : _128066 -> Prop) : (term313 _128066 s) = (term299 _128066 s).
Proof. exact (MK_COMB (@lem6977244) (@lem6977243 _128066 s)). Qed.
Lemma lem6977246 {_128066 : Type'} (s : _128066 -> Prop) : (term314 _128066 s) = (term294 _128066 s).
Proof. exact (eq_refl (term314 _128066 s)). Qed.
Lemma lem6977247 {_128066 : Type'} (s : _128066 -> Prop) : (term315 _128066 s) = (term301 _128066 s).
Proof. exact (MK_COMB (@lem6977245 _128066 s) (@lem6977246 _128066 s)). Qed.
Lemma lem6977248 {_128066 : Type'} : (term316 _128066) = (term302 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977247 _128066 s)). Qed.
Lemma lem6977249 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977250 {_128066 : Type'} : (term308 _128066) = (term303 _128066).
Proof. exact (MK_COMB (@lem6977249 _128066) (@lem6977248 _128066)). Qed.
Lemma lem6977251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977252 {_128066 : Type'} : (term317 _128066) = (term318 _128066).
Proof. exact (MK_COMB (@lem6977251) (@lem6977250 _128066)). Qed.
Lemma lem6977253 {_128066 : Type'} (s : _128066 -> Prop) : (term312 _128066 s) = (term297 _128066 s).
Proof. exact (eq_refl (term312 _128066 s)). Qed.
Lemma lem6977254 {_128066 : Type'} : (term319 _128066) = (term310 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977253 _128066 s)). Qed.
Lemma lem6977255 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977256 {_128066 : Type'} : (term320 _128066) = (term321 _128066).
Proof. exact (MK_COMB (@lem6977255 _128066) (@lem6977254 _128066)). Qed.
Lemma lem6977257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977258 {_128066 : Type'} : (term322 _128066) = (term323 _128066).
Proof. exact (MK_COMB (@lem6977257) (@lem6977256 _128066)). Qed.
Lemma lem6977259 {_128066 : Type'} (s : _128066 -> Prop) : (term314 _128066 s) = (term294 _128066 s).
Proof. exact (eq_refl (term314 _128066 s)). Qed.
Lemma lem6977260 {_128066 : Type'} : (term324 _128066) = (term311 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977259 _128066 s)). Qed.
Lemma lem6977261 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977262 {_128066 : Type'} : (term325 _128066) = (term326 _128066).
Proof. exact (MK_COMB (@lem6977261 _128066) (@lem6977260 _128066)). Qed.
Lemma lem6977263 {_128066 : Type'} : (term309 _128066) = (term327 _128066).
Proof. exact (MK_COMB (@lem6977258 _128066) (@lem6977262 _128066)). Qed.
Lemma lem6977264 {_128066 : Type'} : ((term308 _128066) = (term309 _128066)) = ((term303 _128066) = (term327 _128066)).
Proof. exact (MK_COMB (@lem6977252 _128066) (@lem6977263 _128066)). Qed.
Lemma lem6977265 {_128066 : Type'} : (term303 _128066) = (term327 _128066).
Proof. exact (EQ_MP (@lem6977264 _128066) (@lem6977242 _128066)). Qed.
Lemma lem6977371 {A : Type'} (P : A -> Prop) (Q : Prop) : (term150 A P Q) = (term151 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem6977372 {_128066 : Type'} (P : _128066 -> Prop) (Q : Prop) : (term150 _128066 P Q) = (term151 _128066 P Q).
Proof. exact (@lem6977371 _128066 P Q). Qed.
Lemma lem6977373 {_128066 : Type'} (s : _128066 -> Prop) : (term328 _128066 s) = (term329 _128066 s).
Proof. exact (@lem6977372 _128066 (term30 _128066 s) (s = (@EMPTY _128066))). Qed.
Lemma lem6977374 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term284 _128066 s x) = (@IN _128066 x s).
Proof. exact (eq_refl (term284 _128066 s x)). Qed.
Lemma lem6977375 {_128066 : Type'} (s : _128066 -> Prop) : (term330 _128066 s) = (term30 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977374 _128066 x s)). Qed.
Lemma lem6977376 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6977377 {_128066 : Type'} (s : _128066 -> Prop) : (term331 _128066 s) = (term31 _128066 s).
Proof. exact (MK_COMB (@lem6977376 _128066) (@lem6977375 _128066 s)). Qed.
Lemma lem6977378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977379 {_128066 : Type'} (s : _128066 -> Prop) : (term332 _128066 s) = (term295 _128066 s).
Proof. exact (MK_COMB (@lem6977378) (@lem6977377 _128066 s)). Qed.
Lemma lem6977380 {_128066 : Type'} (s : _128066 -> Prop) : (s = (@EMPTY _128066)) = (s = (@EMPTY _128066)).
Proof. exact (eq_refl (s = (@EMPTY _128066))). Qed.
Lemma lem6977381 {_128066 : Type'} (s : _128066 -> Prop) : (term328 _128066 s) = (term297 _128066 s).
Proof. exact (MK_COMB (@lem6977379 _128066 s) (@lem6977380 _128066 s)). Qed.
Lemma lem6977382 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977383 {_128066 : Type'} (s : _128066 -> Prop) : (term333 _128066 s) = (term334 _128066 s).
Proof. exact (MK_COMB (@lem6977382) (@lem6977381 _128066 s)). Qed.
Lemma lem6977384 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term284 _128066 s x) = (@IN _128066 x s).
Proof. exact (eq_refl (term284 _128066 s x)). Qed.
Lemma lem6977385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977386 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term335 _128066 s x) = (term336 _128066 x s).
Proof. exact (MK_COMB (@lem6977385) (@lem6977384 _128066 x s)). Qed.
Lemma lem6977387 {_128066 : Type'} (s : _128066 -> Prop) : (s = (@EMPTY _128066)) = (s = (@EMPTY _128066)).
Proof. exact (eq_refl (s = (@EMPTY _128066))). Qed.
Lemma lem6977388 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term337 _128066 x s) = (term338 _128066 x s).
Proof. exact (MK_COMB (@lem6977386 _128066 x s) (@lem6977387 _128066 s)). Qed.
Lemma lem6977389 {_128066 : Type'} (s : _128066 -> Prop) : (term339 _128066 s) = (term340 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977388 _128066 x s)). Qed.
Lemma lem6977390 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6977391 {_128066 : Type'} (s : _128066 -> Prop) : (term329 _128066 s) = (term341 _128066 s).
Proof. exact (MK_COMB (@lem6977390 _128066) (@lem6977389 _128066 s)). Qed.
Lemma lem6977392 {_128066 : Type'} (s : _128066 -> Prop) : ((term328 _128066 s) = (term329 _128066 s)) = ((term297 _128066 s) = (term341 _128066 s)).
Proof. exact (MK_COMB (@lem6977383 _128066 s) (@lem6977391 _128066 s)). Qed.
Lemma lem6977393 {_128066 : Type'} (s : _128066 -> Prop) : (term297 _128066 s) = (term341 _128066 s).
Proof. exact (EQ_MP (@lem6977392 _128066 s) (@lem6977373 _128066 s)). Qed.
Lemma lem6977394 {_128066 : Type'} : (term310 _128066) = (term342 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977393 _128066 s)). Qed.
Lemma lem6977395 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977396 {_128066 : Type'} : (term321 _128066) = (term343 _128066).
Proof. exact (MK_COMB (@lem6977395 _128066) (@lem6977394 _128066)). Qed.
Lemma lem6977398 {A B : Type'} (P : type1413 A B) : (term202 A B P) = (term203 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6977399 {_128066 : Type'} (P : type672 _128066) : (term344 _128066 P) = (term345 _128066 P).
Proof. exact (@lem6977398 (_128066 -> Prop) _128066 P). Qed.
Lemma lem6977400 {_128066 : Type'} : (term346 _128066) = (term347 _128066).
Proof. exact (@lem6977399 _128066 (term348 _128066)). Qed.
Lemma lem6977401 {_128066 : Type'} (s : _128066 -> Prop) : (term349 _128066 s) = (term340 _128066 s).
Proof. exact (eq_refl (term349 _128066 s)). Qed.
Lemma lem6977402 {_128066 : Type'} (x : _128066) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6977403 {_128066 : Type'} (s : _128066 -> Prop) (x : _128066) : (term350 _128066 s x) = (term351 _128066 s x).
Proof. exact (MK_COMB (@lem6977401 _128066 s) (@lem6977402 _128066 x)). Qed.
Lemma lem6977404 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term351 _128066 s x) = (term338 _128066 x s).
Proof. exact (eq_refl (term351 _128066 s x)). Qed.
Lemma lem6977405 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term350 _128066 s x) = (term338 _128066 x s).
Proof. exact (TRANS (@lem6977403 _128066 s x) (@lem6977404 _128066 x s)). Qed.
Lemma lem6977406 {_128066 : Type'} (s : _128066 -> Prop) : (term352 _128066 s) = (term340 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977405 _128066 x s)). Qed.
Lemma lem6977407 {_128066 : Type'} : (@ex _128066) = (@ex _128066).
Proof. exact (eq_refl (@ex _128066)). Qed.
Lemma lem6977408 {_128066 : Type'} (s : _128066 -> Prop) : (term353 _128066 s) = (term341 _128066 s).
Proof. exact (MK_COMB (@lem6977407 _128066) (@lem6977406 _128066 s)). Qed.
Lemma lem6977409 {_128066 : Type'} : (term354 _128066) = (term342 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977408 _128066 s)). Qed.
Lemma lem6977410 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977411 {_128066 : Type'} : (term346 _128066) = (term343 _128066).
Proof. exact (MK_COMB (@lem6977410 _128066) (@lem6977409 _128066)). Qed.
Lemma lem6977412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977413 {_128066 : Type'} : (term355 _128066) = (term356 _128066).
Proof. exact (MK_COMB (@lem6977412) (@lem6977411 _128066)). Qed.
Lemma lem6977414 {_128066 : Type'} (s : _128066 -> Prop) : (term349 _128066 s) = (term340 _128066 s).
Proof. exact (eq_refl (term349 _128066 s)). Qed.
Lemma lem6977415 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem6977416 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term357 _128066 x s) = (term358 _128066 x s).
Proof. exact (MK_COMB (@lem6977414 _128066 s) (@lem6977415 _128066 x s)). Qed.
Lemma lem6977417 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term358 _128066 x s) = (term359 _128066 x s).
Proof. exact (eq_refl (term358 _128066 x s)). Qed.
Lemma lem6977418 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term357 _128066 x s) = (term359 _128066 x s).
Proof. exact (TRANS (@lem6977416 _128066 x s) (@lem6977417 _128066 x s)). Qed.
Lemma lem6977419 {_128066 : Type'} (x : type684 _128066) : (term360 _128066 x) = (term361 _128066 x).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977418 _128066 x s)). Qed.
Lemma lem6977420 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977421 {_128066 : Type'} (x : type684 _128066) : (term362 _128066 x) = (term363 _128066 x).
Proof. exact (MK_COMB (@lem6977420 _128066) (@lem6977419 _128066 x)). Qed.
Lemma lem6977422 {_128066 : Type'} : (term364 _128066) = (term365 _128066).
Proof. exact (fun_ext (fun x : type684 _128066 => @lem6977421 _128066 x)). Qed.
Lemma lem6977423 {_128066 : Type'} : (@ex ((_128066 -> Prop) -> _128066)) = (@ex ((_128066 -> Prop) -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> Prop) -> _128066))). Qed.
Lemma lem6977424 {_128066 : Type'} : (term347 _128066) = (term366 _128066).
Proof. exact (MK_COMB (@lem6977423 _128066) (@lem6977422 _128066)). Qed.
Lemma lem6977425 {_128066 : Type'} : ((term346 _128066) = (term347 _128066)) = ((term343 _128066) = (term366 _128066)).
Proof. exact (MK_COMB (@lem6977413 _128066) (@lem6977424 _128066)). Qed.
Lemma lem6977426 {_128066 : Type'} : (term343 _128066) = (term366 _128066).
Proof. exact (EQ_MP (@lem6977425 _128066) (@lem6977400 _128066)). Qed.
Lemma lem6977427 {_128066 : Type'} : (term321 _128066) = (term366 _128066).
Proof. exact (TRANS (@lem6977396 _128066) (@lem6977426 _128066)). Qed.
Lemma lem6977428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977429 {_128066 : Type'} : (term323 _128066) = (term367 _128066).
Proof. exact (MK_COMB (@lem6977428) (@lem6977427 _128066)). Qed.
Lemma lem6977430 {_128066 : Type'} : (term326 _128066) = (term326 _128066).
Proof. exact (eq_refl (term326 _128066)). Qed.
Lemma lem6977431 {_128066 : Type'} : (term327 _128066) = (term368 _128066).
Proof. exact (MK_COMB (@lem6977429 _128066) (@lem6977430 _128066)). Qed.
Lemma lem6977433 {A : Type'} (P : A -> Prop) (Q : Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6977434 {_128066 : Type'} (P : type162 _128066) (Q : Prop) : (term371 _128066 P Q) = (term372 _128066 P Q).
Proof. exact (@lem6977433 (type684 _128066) P Q). Qed.
Lemma lem6977435 {_128066 : Type'} : (term373 _128066) = (term374 _128066).
Proof. exact (@lem6977434 _128066 (term365 _128066) (term326 _128066)). Qed.
Lemma lem6977436 {_128066 : Type'} (x : type684 _128066) : (term375 _128066 x) = (term363 _128066 x).
Proof. exact (eq_refl (term375 _128066 x)). Qed.
Lemma lem6977437 {_128066 : Type'} : (term376 _128066) = (term365 _128066).
Proof. exact (fun_ext (fun x : type684 _128066 => @lem6977436 _128066 x)). Qed.
Lemma lem6977438 {_128066 : Type'} : (@ex ((_128066 -> Prop) -> _128066)) = (@ex ((_128066 -> Prop) -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> Prop) -> _128066))). Qed.
Lemma lem6977439 {_128066 : Type'} : (term377 _128066) = (term366 _128066).
Proof. exact (MK_COMB (@lem6977438 _128066) (@lem6977437 _128066)). Qed.
Lemma lem6977440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977441 {_128066 : Type'} : (term378 _128066) = (term367 _128066).
Proof. exact (MK_COMB (@lem6977440) (@lem6977439 _128066)). Qed.
Lemma lem6977442 {_128066 : Type'} : (term326 _128066) = (term326 _128066).
Proof. exact (eq_refl (term326 _128066)). Qed.
Lemma lem6977443 {_128066 : Type'} : (term373 _128066) = (term368 _128066).
Proof. exact (MK_COMB (@lem6977441 _128066) (@lem6977442 _128066)). Qed.
Lemma lem6977444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6977445 {_128066 : Type'} : (term379 _128066) = (term380 _128066).
Proof. exact (MK_COMB (@lem6977444) (@lem6977443 _128066)). Qed.
Lemma lem6977446 {_128066 : Type'} (x : type684 _128066) : (term375 _128066 x) = (term363 _128066 x).
Proof. exact (eq_refl (term375 _128066 x)). Qed.
Lemma lem6977447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977448 {_128066 : Type'} (x : type684 _128066) : (term381 _128066 x) = (term382 _128066 x).
Proof. exact (MK_COMB (@lem6977447) (@lem6977446 _128066 x)). Qed.
Lemma lem6977449 {_128066 : Type'} : (term326 _128066) = (term326 _128066).
Proof. exact (eq_refl (term326 _128066)). Qed.
Lemma lem6977450 {_128066 : Type'} (x : type684 _128066) : (term383 _128066 x) = (term384 _128066 x).
Proof. exact (MK_COMB (@lem6977448 _128066 x) (@lem6977449 _128066)). Qed.
Lemma lem6977451 {_128066 : Type'} : (term385 _128066) = (term386 _128066).
Proof. exact (fun_ext (fun x : type684 _128066 => @lem6977450 _128066 x)). Qed.
Lemma lem6977452 {_128066 : Type'} : (@ex ((_128066 -> Prop) -> _128066)) = (@ex ((_128066 -> Prop) -> _128066)).
Proof. exact (eq_refl (@ex ((_128066 -> Prop) -> _128066))). Qed.
Lemma lem6977453 {_128066 : Type'} : (term374 _128066) = (term387 _128066).
Proof. exact (MK_COMB (@lem6977452 _128066) (@lem6977451 _128066)). Qed.
Lemma lem6977454 {_128066 : Type'} : ((term373 _128066) = (term374 _128066)) = ((term368 _128066) = (term387 _128066)).
Proof. exact (MK_COMB (@lem6977445 _128066) (@lem6977453 _128066)). Qed.
Lemma lem6977455 {_128066 : Type'} : (term368 _128066) = (term387 _128066).
Proof. exact (EQ_MP (@lem6977454 _128066) (@lem6977435 _128066)). Qed.
Lemma lem6977456 {_128066 : Type'} : (term327 _128066) = (term387 _128066).
Proof. exact (TRANS (@lem6977431 _128066) (@lem6977455 _128066)). Qed.
Lemma lem6977457 {_128066 : Type'} : (term303 _128066) = (term387 _128066).
Proof. exact (TRANS (@lem6977265 _128066) (@lem6977456 _128066)). Qed.
Lemma lem6977458 {_128066 : Type'} : (term11 _128066) = (term387 _128066).
Proof. exact (TRANS (@lem6977238 _128066) (@lem6977457 _128066)). Qed.
Lemma lem6977459 {_128066 : Type'} (h1 : term11 _128066) : term387 _128066.
Proof. exact (EQ_MP (@lem6977458 _128066) (@lem6976184 _128066 h1)). Qed.
Lemma lem6977460 {_128066 : Type'} (x : type684 _128066) (h1 : term384 _128066 x) : term384 _128066 x.
Proof. exact (h1). Qed.
Lemma lem6977462 {_128066 : Type'} (x'' : type642 _128066) (h1 : term273 _128066 x'') : term273 _128066 x''.
Proof. exact (h1). Qed.
Lemma lem6977463 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term99 _128066 s) : term99 _128066 s.
Proof. exact (h1). Qed.
Lemma lem6977464 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (h1 : term90 _128066 f s) : term90 _128066 f s.
Proof. exact (h1). Qed.
Lemma lem6977465 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term80 _128066 f s b.
Proof. exact (h1). Qed.
Lemma lem6977472 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977473 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6977472 nat (nat -> Prop) f x). Qed.
Lemma lem6977474 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem6977473 Peano.le m). Qed.
Lemma lem6977475 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6977476 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem6977474 m) (@lem6977475 n)). Qed.
Lemma lem6977478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977479 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6977478 nat Prop f x). Qed.
Lemma lem6977480 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term388 m n).
Proof. exact (@lem6977479 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem6977482 (m : nat) (n : nat) : (Peano.le m n) = (term388 m n).
Proof. exact (TRANS (@lem6977476 m n) (@lem6977480 m n)). Qed.
Lemma lem6977483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977491 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6977490 nat (nat -> Prop) f x). Qed.
Lemma lem6977492 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem6977491 Peano.lt m). Qed.
Lemma lem6977493 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem6977494 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem6977492 m) (@lem6977493 n)). Qed.
Lemma lem6977496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977497 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6977496 nat Prop f x). Qed.
Lemma lem6977498 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term389 m n).
Proof. exact (@lem6977497 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem6977500 (m : nat) (n : nat) : (Peano.lt m n) = (term389 m n).
Proof. exact (TRANS (@lem6977494 m n) (@lem6977498 m n)). Qed.
Lemma lem6977501 (m : nat) (n : nat) : (term390 m n) = (term391 m n).
Proof. exact (MK_COMB (@lem6977483) (@lem6977500 m n)). Qed.
Lemma lem6977502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977503 (m : nat) (n : nat) : (term392 m n) = (term393 m n).
Proof. exact (MK_COMB (@lem6977502) (@lem6977501 m n)). Qed.
Lemma lem6977504 (m : nat) (n : nat) : (term277 m n) = (term394 m n).
Proof. exact (MK_COMB (@lem6977503 m n) (@lem6977482 m n)). Qed.
Lemma lem6977505 (m : nat) : (term278 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem6977504 m n)). Qed.
Lemma lem6977506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977507 (m : nat) : (term279 m) = (term396 m).
Proof. exact (MK_COMB (@lem6977506) (@lem6977505 m)). Qed.
Lemma lem6977508 : term280 = term397.
Proof. exact (fun_ext (fun m : nat => @lem6977507 m)). Qed.
Lemma lem6977509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6977510 : term281 = term398.
Proof. exact (MK_COMB (@lem6977509) (@lem6977508)). Qed.
Lemma lem6977511 (h1 : term38) : term398.
Proof. exact (EQ_MP (@lem6977510) (@lem6977205 h1)). Qed.
Lemma lem6977518 {_128066 : Type'} (s : _128066 -> Prop) : (term29 _128066 s) = (term29 _128066 s).
Proof. exact (eq_refl (term29 _128066 s)). Qed.
Lemma lem6977519 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977526 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977527 {_128066 : Type'} (f : type1364 _128066) (x : _128066) : (f x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977526 _128066 (type686 _128066) f x). Qed.
Lemma lem6977528 {_128066 : Type'} (x : _128066) : (@IN _128066 x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x).
Proof. exact (@lem6977527 _128066 (@IN _128066) x). Qed.
Lemma lem6977529 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6977530 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s).
Proof. exact (MK_COMB (@lem6977528 _128066 x) (@lem6977529 _128066 s)). Qed.
Lemma lem6977532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977533 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977532 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6977534 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s) = (term399 _128066 x s).
Proof. exact (@lem6977533 _128066 (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x) s). Qed.
Lemma lem6977536 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (term399 _128066 x s).
Proof. exact (TRANS (@lem6977530 _128066 x s) (@lem6977534 _128066 x s)). Qed.
Lemma lem6977537 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term286 _128066 x s) = (term400 _128066 x s).
Proof. exact (MK_COMB (@lem6977519) (@lem6977536 _128066 x s)). Qed.
Lemma lem6977538 {_128066 : Type'} (s : _128066 -> Prop) : (term288 _128066 s) = (term401 _128066 s).
Proof. exact (fun_ext (fun x : _128066 => @lem6977537 _128066 x s)). Qed.
Lemma lem6977539 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6977540 {_128066 : Type'} (s : _128066 -> Prop) : (term289 _128066 s) = (term402 _128066 s).
Proof. exact (MK_COMB (@lem6977539 _128066) (@lem6977538 _128066 s)). Qed.
Lemma lem6977541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977542 {_128066 : Type'} (s : _128066 -> Prop) : (term292 _128066 s) = (term403 _128066 s).
Proof. exact (MK_COMB (@lem6977541) (@lem6977540 _128066 s)). Qed.
Lemma lem6977543 {_128066 : Type'} (s : _128066 -> Prop) : (term294 _128066 s) = (term404 _128066 s).
Proof. exact (MK_COMB (@lem6977542 _128066 s) (@lem6977518 _128066 s)). Qed.
Lemma lem6977544 {_128066 : Type'} : (term311 _128066) = (term405 _128066).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977543 _128066 s)). Qed.
Lemma lem6977545 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977546 {_128066 : Type'} : (term326 _128066) = (term406 _128066).
Proof. exact (MK_COMB (@lem6977545 _128066) (@lem6977544 _128066)). Qed.
Lemma lem6977551 {_128066 : Type'} (s : _128066 -> Prop) : (s = (@EMPTY _128066)) = (s = (@EMPTY _128066)).
Proof. exact (eq_refl (s = (@EMPTY _128066))). Qed.
Lemma lem6977552 {_128066 : Type'} : (@IN _128066) = (@IN _128066).
Proof. exact (eq_refl (@IN _128066)). Qed.
Lemma lem6977557 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977558 {_128066 : Type'} (f : type684 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> _128066) f x).
Proof. exact (@lem6977557 (_128066 -> Prop) _128066 f x). Qed.
Lemma lem6977560 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (x s) = (@I ((_128066 -> Prop) -> _128066) x s).
Proof. exact (@lem6977558 _128066 x s). Qed.
Lemma lem6977561 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6977562 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term407 _128066 x s) = (term408 _128066 x s).
Proof. exact (MK_COMB (@lem6977552 _128066) (@lem6977560 _128066 x s)). Qed.
Lemma lem6977563 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term409 _128066 x s) = (term410 _128066 x s).
Proof. exact (MK_COMB (@lem6977562 _128066 x s) (@lem6977561 _128066 s)). Qed.
Lemma lem6977565 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977566 {_128066 : Type'} (f : type1364 _128066) (x : _128066) : (f x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977565 _128066 (type686 _128066) f x). Qed.
Lemma lem6977567 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term408 _128066 x s) = (term411 _128066 x s).
Proof. exact (@lem6977566 _128066 (@IN _128066) (@I ((_128066 -> Prop) -> _128066) x s)). Qed.
Lemma lem6977568 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6977569 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term410 _128066 x s) = (term412 _128066 x s).
Proof. exact (MK_COMB (@lem6977567 _128066 x s) (@lem6977568 _128066 s)). Qed.
Lemma lem6977571 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977572 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977571 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6977573 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term412 _128066 x s) = (term413 _128066 x s).
Proof. exact (@lem6977572 _128066 (term411 _128066 x s) s). Qed.
Lemma lem6977574 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term410 _128066 x s) = (term413 _128066 x s).
Proof. exact (TRANS (@lem6977569 _128066 x s) (@lem6977573 _128066 x s)). Qed.
Lemma lem6977575 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term409 _128066 x s) = (term413 _128066 x s).
Proof. exact (TRANS (@lem6977563 _128066 x s) (@lem6977574 _128066 x s)). Qed.
Lemma lem6977576 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977577 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term414 _128066 x s) = (term415 _128066 x s).
Proof. exact (MK_COMB (@lem6977576) (@lem6977575 _128066 x s)). Qed.
Lemma lem6977578 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term359 _128066 x s) = (term416 _128066 x s).
Proof. exact (MK_COMB (@lem6977577 _128066 x s) (@lem6977551 _128066 s)). Qed.
Lemma lem6977579 {_128066 : Type'} (x : type684 _128066) : (term361 _128066 x) = (term417 _128066 x).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6977578 _128066 x s)). Qed.
Lemma lem6977580 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6977581 {_128066 : Type'} (x : type684 _128066) : (term363 _128066 x) = (term418 _128066 x).
Proof. exact (MK_COMB (@lem6977580 _128066) (@lem6977579 _128066 x)). Qed.
Lemma lem6977582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6977583 {_128066 : Type'} (x : type684 _128066) : (term382 _128066 x) = (term419 _128066 x).
Proof. exact (MK_COMB (@lem6977582) (@lem6977581 _128066 x)). Qed.
Lemma lem6977584 {_128066 : Type'} (x : type684 _128066) : (term384 _128066 x) = (term420 _128066 x).
Proof. exact (MK_COMB (@lem6977583 _128066 x) (@lem6977546 _128066)). Qed.
Lemma lem6977585 {_128066 : Type'} (x : type684 _128066) (h1 : term384 _128066 x) : term420 _128066 x.
Proof. exact (EQ_MP (@lem6977584 _128066 x) (@lem6977460 _128066 x h1)). Qed.
Lemma lem6977817 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6977824 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977825 {_128066 : Type'} (f : type644 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) f x).
Proof. exact (@lem6977824 (_128066 -> Prop) (type705 _128066) f x). Qed.
Lemma lem6977826 {_128066 : Type'} (s : _128066 -> Prop) : (@nsum _128066 s) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s).
Proof. exact (@lem6977825 _128066 (@nsum _128066) s). Qed.
Lemma lem6977827 {_128066 : Type'} (f : _128066 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6977828 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@nsum _128066 s f) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s f).
Proof. exact (MK_COMB (@lem6977826 _128066 s) (@lem6977827 _128066 f)). Qed.
Lemma lem6977830 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977831 {_128066 : Type'} (f : type705 _128066) (x : _128066 -> nat) : (f x) = (@I ((_128066 -> nat) -> nat) f x).
Proof. exact (@lem6977830 (_128066 -> nat) nat f x). Qed.
Lemma lem6977832 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s f) = (term421 _128066 s f).
Proof. exact (@lem6977831 _128066 (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s) f). Qed.
Lemma lem6977834 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@nsum _128066 s f) = (term421 _128066 s f).
Proof. exact (TRANS (@lem6977828 _128066 s f) (@lem6977832 _128066 s f)). Qed.
Lemma lem6977835 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6977840 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977841 {_128066 : Type'} (f : type687 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> nat) f x).
Proof. exact (@lem6977840 (_128066 -> Prop) nat f x). Qed.
Lemma lem6977843 {_128066 : Type'} (s : _128066 -> Prop) : (@CARD _128066 s) = (@I ((_128066 -> Prop) -> nat) (@CARD _128066) s).
Proof. exact (@lem6977841 _128066 (@CARD _128066) s). Qed.
Lemma lem6977844 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977845 {_128066 : Type'} (s : _128066 -> Prop) : (term422 _128066 s) = (term423 _128066 s).
Proof. exact (MK_COMB (@lem6977835) (@lem6977843 _128066 s)). Qed.
Lemma lem6977846 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term424 _128066 s b) = (term425 _128066 s b).
Proof. exact (MK_COMB (@lem6977845 _128066 s) (@lem6977844 b)). Qed.
Lemma lem6977848 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977849 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem6977848 nat (nat -> nat) f x). Qed.
Lemma lem6977850 {_128066 : Type'} (s : _128066 -> Prop) : (term423 _128066 s) = (term426 _128066 s).
Proof. exact (@lem6977849 Nat.mul (@I ((_128066 -> Prop) -> nat) (@CARD _128066) s)). Qed.
Lemma lem6977851 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977852 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term425 _128066 s b) = (term427 _128066 s b).
Proof. exact (MK_COMB (@lem6977850 _128066 s) (@lem6977851 b)). Qed.
Lemma lem6977854 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977855 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6977854 nat nat f x). Qed.
Lemma lem6977856 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term427 _128066 s b) = (term428 _128066 s b).
Proof. exact (@lem6977855 (term426 _128066 s) b). Qed.
Lemma lem6977857 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term425 _128066 s b) = (term428 _128066 s b).
Proof. exact (TRANS (@lem6977852 _128066 s b) (@lem6977856 _128066 s b)). Qed.
Lemma lem6977858 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term424 _128066 s b) = (term428 _128066 s b).
Proof. exact (TRANS (@lem6977846 _128066 s b) (@lem6977857 _128066 s b)). Qed.
Lemma lem6977859 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (term429 _128066 s f) = (term430 _128066 s f).
Proof. exact (MK_COMB (@lem6977817) (@lem6977834 _128066 s f)). Qed.
Lemma lem6977860 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term431 _128066 f s b).
Proof. exact (MK_COMB (@lem6977859 _128066 s f) (@lem6977858 _128066 s b)). Qed.
Lemma lem6977862 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977863 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6977862 nat (nat -> Prop) f x). Qed.
Lemma lem6977864 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (term430 _128066 s f) = (term432 _128066 s f).
Proof. exact (@lem6977863 Peano.lt (term421 _128066 s f)). Qed.
Lemma lem6977865 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term428 _128066 s b) = (term428 _128066 s b).
Proof. exact (eq_refl (term428 _128066 s b)). Qed.
Lemma lem6977866 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term431 _128066 f s b) = (term433 _128066 f s b).
Proof. exact (MK_COMB (@lem6977864 _128066 s f) (@lem6977865 _128066 s b)). Qed.
Lemma lem6977868 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977869 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6977868 nat Prop f x). Qed.
Lemma lem6977870 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term433 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (@lem6977869 (term432 _128066 s f) (term428 _128066 s b)). Qed.
Lemma lem6977871 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term431 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (TRANS (@lem6977866 _128066 f s b) (@lem6977870 _128066 f s b)). Qed.
Lemma lem6977872 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (TRANS (@lem6977860 _128066 f s b) (@lem6977871 _128066 f s b)). Qed.
Lemma lem6977873 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977874 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6977879 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977881 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (f x) = (@I (_128066 -> nat) f x).
Proof. exact (@lem6977879 _128066 nat f x). Qed.
Lemma lem6977882 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977883 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (term435 _128066 f x) = (term436 _128066 f x).
Proof. exact (MK_COMB (@lem6977874) (@lem6977881 _128066 f x)). Qed.
Lemma lem6977884 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term71 _128066 f x b) = (term437 _128066 f x b).
Proof. exact (MK_COMB (@lem6977883 _128066 f x) (@lem6977882 b)). Qed.
Lemma lem6977886 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977887 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6977886 nat (nat -> Prop) f x). Qed.
Lemma lem6977888 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (term436 _128066 f x) = (term438 _128066 f x).
Proof. exact (@lem6977887 Peano.lt (@I (_128066 -> nat) f x)). Qed.
Lemma lem6977889 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977890 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term437 _128066 f x b) = (term439 _128066 f x b).
Proof. exact (MK_COMB (@lem6977888 _128066 f x) (@lem6977889 b)). Qed.
Lemma lem6977892 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977893 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6977892 nat Prop f x). Qed.
Lemma lem6977894 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term439 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (@lem6977893 (term438 _128066 f x) b). Qed.
Lemma lem6977895 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term437 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (TRANS (@lem6977890 _128066 f x b) (@lem6977894 _128066 f x b)). Qed.
Lemma lem6977896 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term71 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (TRANS (@lem6977884 _128066 f x b) (@lem6977895 _128066 f x b)). Qed.
Lemma lem6977897 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term441 _128066 f x b) = (term442 _128066 f x b).
Proof. exact (MK_COMB (@lem6977873) (@lem6977896 _128066 f x b)). Qed.
Lemma lem6977898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977905 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977906 {_128066 : Type'} (f : type1364 _128066) (x : _128066) : (f x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977905 _128066 (type686 _128066) f x). Qed.
Lemma lem6977907 {_128066 : Type'} (x : _128066) : (@IN _128066 x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x).
Proof. exact (@lem6977906 _128066 (@IN _128066) x). Qed.
Lemma lem6977908 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6977909 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s).
Proof. exact (MK_COMB (@lem6977907 _128066 x) (@lem6977908 _128066 s)). Qed.
Lemma lem6977911 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977912 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6977911 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6977913 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s) = (term399 _128066 x s).
Proof. exact (@lem6977912 _128066 (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x) s). Qed.
Lemma lem6977915 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (term399 _128066 x s).
Proof. exact (TRANS (@lem6977909 _128066 x s) (@lem6977913 _128066 x s)). Qed.
Lemma lem6977916 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term286 _128066 x s) = (term400 _128066 x s).
Proof. exact (MK_COMB (@lem6977898) (@lem6977915 _128066 x s)). Qed.
Lemma lem6977917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6977918 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term443 _128066 x s) = (term444 _128066 x s).
Proof. exact (MK_COMB (@lem6977917) (@lem6977916 _128066 x s)). Qed.
Lemma lem6977919 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term121 _128066 s f x b) = (term445 _128066 s f x b).
Proof. exact (MK_COMB (@lem6977918 _128066 x s) (@lem6977897 _128066 f x b)). Qed.
Lemma lem6977920 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term129 _128066 s f b) = (term446 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6977919 _128066 s f x b)). Qed.
Lemma lem6977921 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6977922 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term130 _128066 s f b) = (term447 _128066 s f b).
Proof. exact (MK_COMB (@lem6977921 _128066) (@lem6977920 _128066 s f b)). Qed.
Lemma lem6977923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6977924 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem6977925 {_128066 : Type'} (f : _128066 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6977934 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977935 {_128066 : Type'} (f : type642 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) f x).
Proof. exact (@lem6977934 (_128066 -> Prop) (type702 _128066) f x). Qed.
Lemma lem6977936 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (x'' s) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s).
Proof. exact (@lem6977935 _128066 x'' s). Qed.
Lemma lem6977937 {_128066 : Type'} (f : _128066 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6977938 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (x'' s f) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s f).
Proof. exact (MK_COMB (@lem6977936 _128066 x'' s) (@lem6977937 _128066 f)). Qed.
Lemma lem6977940 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977941 {_128066 : Type'} (f : type702 _128066) (x : _128066 -> nat) : (f x) = (@I ((_128066 -> nat) -> nat -> _128066) f x).
Proof. exact (@lem6977940 (_128066 -> nat) (nat -> _128066) f x). Qed.
Lemma lem6977942 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s f) = (term448 _128066 x'' s f).
Proof. exact (@lem6977941 _128066 (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s) f). Qed.
Lemma lem6977943 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (x'' s f) = (term448 _128066 x'' s f).
Proof. exact (TRANS (@lem6977938 _128066 x'' s f) (@lem6977942 _128066 x'' s f)). Qed.
Lemma lem6977944 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977945 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (x'' s f b) = (term449 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977943 _128066 x'' s f) (@lem6977944 b)). Qed.
Lemma lem6977947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977948 {_128066 : Type'} (f : nat -> _128066) (x : nat) : (f x) = (@I (nat -> _128066) f x).
Proof. exact (@lem6977947 nat _128066 f x). Qed.
Lemma lem6977949 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term449 _128066 x'' s f b) = (term450 _128066 x'' s f b).
Proof. exact (@lem6977948 _128066 (term448 _128066 x'' s f) b). Qed.
Lemma lem6977951 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (x'' s f b) = (term450 _128066 x'' s f b).
Proof. exact (TRANS (@lem6977945 _128066 x'' s f b) (@lem6977949 _128066 x'' s f b)). Qed.
Lemma lem6977952 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term451 _128066 x'' s f b) = (term452 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977925 _128066 f) (@lem6977951 _128066 x'' s f b)). Qed.
Lemma lem6977954 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977955 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (f x) = (@I (_128066 -> nat) f x).
Proof. exact (@lem6977954 _128066 nat f x). Qed.
Lemma lem6977956 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term452 _128066 x'' s f b) = (term453 _128066 x'' s f b).
Proof. exact (@lem6977955 _128066 f (term450 _128066 x'' s f b)). Qed.
Lemma lem6977957 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term451 _128066 x'' s f b) = (term453 _128066 x'' s f b).
Proof. exact (TRANS (@lem6977952 _128066 x'' s f b) (@lem6977956 _128066 x'' s f b)). Qed.
Lemma lem6977958 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977959 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term454 _128066 x'' s f b) = (term455 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977924) (@lem6977957 _128066 x'' s f b)). Qed.
Lemma lem6977960 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term456 _128066 x'' s f b) = (term457 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977959 _128066 x'' s f b) (@lem6977958 b)). Qed.
Lemma lem6977962 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977963 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6977962 nat (nat -> Prop) f x). Qed.
Lemma lem6977964 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term455 _128066 x'' s f b) = (term458 _128066 x'' s f b).
Proof. exact (@lem6977963 Peano.le (term453 _128066 x'' s f b)). Qed.
Lemma lem6977965 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977966 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term457 _128066 x'' s f b) = (term459 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977964 _128066 x'' s f b) (@lem6977965 b)). Qed.
Lemma lem6977968 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977969 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6977968 nat Prop f x). Qed.
Lemma lem6977970 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term459 _128066 x'' s f b) = (term460 _128066 x'' s f b).
Proof. exact (@lem6977969 (term458 _128066 x'' s f b) b). Qed.
Lemma lem6977971 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term457 _128066 x'' s f b) = (term460 _128066 x'' s f b).
Proof. exact (TRANS (@lem6977966 _128066 x'' s f b) (@lem6977970 _128066 x'' s f b)). Qed.
Lemma lem6977972 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term456 _128066 x'' s f b) = (term460 _128066 x'' s f b).
Proof. exact (TRANS (@lem6977960 _128066 x'' s f b) (@lem6977971 _128066 x'' s f b)). Qed.
Lemma lem6977973 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term461 _128066 x'' s f b) = (term462 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977923) (@lem6977972 _128066 x'' s f b)). Qed.
Lemma lem6977974 {_128066 : Type'} : (@IN _128066) = (@IN _128066).
Proof. exact (eq_refl (@IN _128066)). Qed.
Lemma lem6977983 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977984 {_128066 : Type'} (f : type642 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) f x).
Proof. exact (@lem6977983 (_128066 -> Prop) (type702 _128066) f x). Qed.
Lemma lem6977985 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (x'' s) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s).
Proof. exact (@lem6977984 _128066 x'' s). Qed.
Lemma lem6977986 {_128066 : Type'} (f : _128066 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6977987 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (x'' s f) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s f).
Proof. exact (MK_COMB (@lem6977985 _128066 x'' s) (@lem6977986 _128066 f)). Qed.
Lemma lem6977989 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977990 {_128066 : Type'} (f : type702 _128066) (x : _128066 -> nat) : (f x) = (@I ((_128066 -> nat) -> nat -> _128066) f x).
Proof. exact (@lem6977989 (_128066 -> nat) (nat -> _128066) f x). Qed.
Lemma lem6977991 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s f) = (term448 _128066 x'' s f).
Proof. exact (@lem6977990 _128066 (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat -> _128066) x'' s) f). Qed.
Lemma lem6977992 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) : (x'' s f) = (term448 _128066 x'' s f).
Proof. exact (TRANS (@lem6977987 _128066 x'' s f) (@lem6977991 _128066 x'' s f)). Qed.
Lemma lem6977993 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6977994 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (x'' s f b) = (term449 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977992 _128066 x'' s f) (@lem6977993 b)). Qed.
Lemma lem6977996 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6977997 {_128066 : Type'} (f : nat -> _128066) (x : nat) : (f x) = (@I (nat -> _128066) f x).
Proof. exact (@lem6977996 nat _128066 f x). Qed.
Lemma lem6977998 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term449 _128066 x'' s f b) = (term450 _128066 x'' s f b).
Proof. exact (@lem6977997 _128066 (term448 _128066 x'' s f) b). Qed.
Lemma lem6978000 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (x'' s f b) = (term450 _128066 x'' s f b).
Proof. exact (TRANS (@lem6977994 _128066 x'' s f b) (@lem6977998 _128066 x'' s f b)). Qed.
Lemma lem6978001 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6978002 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term463 _128066 x'' s f b) = (term464 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6977974 _128066) (@lem6978000 _128066 x'' s f b)). Qed.
Lemma lem6978003 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term465 _128066 x'' f b s) = (term466 _128066 x'' f b s).
Proof. exact (MK_COMB (@lem6978002 _128066 x'' s f b) (@lem6978001 _128066 s)). Qed.
Lemma lem6978005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978006 {_128066 : Type'} (f : type1364 _128066) (x : _128066) : (f x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978005 _128066 (type686 _128066) f x). Qed.
Lemma lem6978007 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term464 _128066 x'' s f b) = (term467 _128066 x'' s f b).
Proof. exact (@lem6978006 _128066 (@IN _128066) (term450 _128066 x'' s f b)). Qed.
Lemma lem6978008 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6978009 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term466 _128066 x'' f b s) = (term468 _128066 x'' f b s).
Proof. exact (MK_COMB (@lem6978007 _128066 x'' s f b) (@lem6978008 _128066 s)). Qed.
Lemma lem6978011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978012 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978011 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6978013 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term468 _128066 x'' f b s) = (term469 _128066 x'' f b s).
Proof. exact (@lem6978012 _128066 (term467 _128066 x'' s f b) s). Qed.
Lemma lem6978014 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term466 _128066 x'' f b s) = (term469 _128066 x'' f b s).
Proof. exact (TRANS (@lem6978009 _128066 x'' f b s) (@lem6978013 _128066 x'' f b s)). Qed.
Lemma lem6978015 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term465 _128066 x'' f b s) = (term469 _128066 x'' f b s).
Proof. exact (TRANS (@lem6978003 _128066 x'' f b s) (@lem6978014 _128066 x'' f b s)). Qed.
Lemma lem6978016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6978017 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term470 _128066 x'' f b s) = (term471 _128066 x'' f b s).
Proof. exact (MK_COMB (@lem6978016) (@lem6978015 _128066 x'' f b s)). Qed.
Lemma lem6978018 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term472 _128066 x'' s f b) = (term473 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978017 _128066 x'' f b s) (@lem6977973 _128066 x'' s f b)). Qed.
Lemma lem6978019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978020 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term474 _128066 x'' s f b) = (term475 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978019) (@lem6978018 _128066 x'' s f b)). Qed.
Lemma lem6978021 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term476 _128066 x'' s f b) = (term477 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978020 _128066 x'' s f b) (@lem6977922 _128066 s f b)). Qed.
Lemma lem6978022 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6978027 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978028 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978027 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6978030 {_128066 : Type'} (s : _128066 -> Prop) : (@FINITE _128066 s) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s).
Proof. exact (@lem6978028 _128066 (@FINITE _128066) s). Qed.
Lemma lem6978031 {_128066 : Type'} (s : _128066 -> Prop) : (term172 _128066 s) = (term478 _128066 s).
Proof. exact (MK_COMB (@lem6978022) (@lem6978030 _128066 s)). Qed.
Lemma lem6978032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978033 {_128066 : Type'} (s : _128066 -> Prop) : (term136 _128066 s) = (term479 _128066 s).
Proof. exact (MK_COMB (@lem6978032) (@lem6978031 _128066 s)). Qed.
Lemma lem6978034 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term480 _128066 x'' s f b) = (term481 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978033 _128066 s) (@lem6978021 _128066 x'' s f b)). Qed.
Lemma lem6978035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978036 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term482 _128066 x'' s f b) = (term483 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978035) (@lem6978034 _128066 x'' s f b)). Qed.
Lemma lem6978037 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term484 _128066 x'' f s b) = (term485 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978036 _128066 x'' s f b) (@lem6977872 _128066 f s b)). Qed.
Lemma lem6978038 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term486 _128066 x'' f s) = (term487 _128066 x'' f s).
Proof. exact (fun_ext (fun b : nat => @lem6978037 _128066 x'' f s b)). Qed.
Lemma lem6978039 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6978040 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term488 _128066 x'' f s) = (term489 _128066 x'' f s).
Proof. exact (MK_COMB (@lem6978039) (@lem6978038 _128066 x'' f s)). Qed.
Lemma lem6978041 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term490 _128066 x'' s) = (term491 _128066 x'' s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6978040 _128066 x'' f s)). Qed.
Lemma lem6978042 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6978043 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term269 _128066 x'' s) = (term492 _128066 x'' s).
Proof. exact (MK_COMB (@lem6978042 _128066) (@lem6978041 _128066 x'' s)). Qed.
Lemma lem6978044 {_128066 : Type'} (x'' : type642 _128066) : (term271 _128066 x'') = (term493 _128066 x'').
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6978043 _128066 x'' s)). Qed.
Lemma lem6978045 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6978046 {_128066 : Type'} (x'' : type642 _128066) : (term273 _128066 x'') = (term494 _128066 x'').
Proof. exact (MK_COMB (@lem6978045 _128066) (@lem6978044 _128066 x'')). Qed.
Lemma lem6978047 {_128066 : Type'} (x'' : type642 _128066) (h1 : term273 _128066 x'') : term494 _128066 x''.
Proof. exact (EQ_MP (@lem6978046 _128066 x'') (@lem6977462 _128066 x'' h1)). Qed.
Lemma lem6978048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6978049 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6978056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978057 {_128066 : Type'} (f : type644 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) f x).
Proof. exact (@lem6978056 (_128066 -> Prop) (type705 _128066) f x). Qed.
Lemma lem6978058 {_128066 : Type'} (s : _128066 -> Prop) : (@nsum _128066 s) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s).
Proof. exact (@lem6978057 _128066 (@nsum _128066) s). Qed.
Lemma lem6978059 {_128066 : Type'} (f : _128066 -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6978060 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@nsum _128066 s f) = (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s f).
Proof. exact (MK_COMB (@lem6978058 _128066 s) (@lem6978059 _128066 f)). Qed.
Lemma lem6978062 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978063 {_128066 : Type'} (f : type705 _128066) (x : _128066 -> nat) : (f x) = (@I ((_128066 -> nat) -> nat) f x).
Proof. exact (@lem6978062 (_128066 -> nat) nat f x). Qed.
Lemma lem6978064 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s f) = (term421 _128066 s f).
Proof. exact (@lem6978063 _128066 (@I ((_128066 -> Prop) -> (_128066 -> nat) -> nat) (@nsum _128066) s) f). Qed.
Lemma lem6978066 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (@nsum _128066 s f) = (term421 _128066 s f).
Proof. exact (TRANS (@lem6978060 _128066 s f) (@lem6978064 _128066 s f)). Qed.
Lemma lem6978067 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6978072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978073 {_128066 : Type'} (f : type687 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> nat) f x).
Proof. exact (@lem6978072 (_128066 -> Prop) nat f x). Qed.
Lemma lem6978075 {_128066 : Type'} (s : _128066 -> Prop) : (@CARD _128066 s) = (@I ((_128066 -> Prop) -> nat) (@CARD _128066) s).
Proof. exact (@lem6978073 _128066 (@CARD _128066) s). Qed.
Lemma lem6978076 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6978077 {_128066 : Type'} (s : _128066 -> Prop) : (term422 _128066 s) = (term423 _128066 s).
Proof. exact (MK_COMB (@lem6978067) (@lem6978075 _128066 s)). Qed.
Lemma lem6978078 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term424 _128066 s b) = (term425 _128066 s b).
Proof. exact (MK_COMB (@lem6978077 _128066 s) (@lem6978076 b)). Qed.
Lemma lem6978080 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978081 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem6978080 nat (nat -> nat) f x). Qed.
Lemma lem6978082 {_128066 : Type'} (s : _128066 -> Prop) : (term423 _128066 s) = (term426 _128066 s).
Proof. exact (@lem6978081 Nat.mul (@I ((_128066 -> Prop) -> nat) (@CARD _128066) s)). Qed.
Lemma lem6978083 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6978084 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term425 _128066 s b) = (term427 _128066 s b).
Proof. exact (MK_COMB (@lem6978082 _128066 s) (@lem6978083 b)). Qed.
Lemma lem6978086 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978087 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem6978086 nat nat f x). Qed.
Lemma lem6978088 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term427 _128066 s b) = (term428 _128066 s b).
Proof. exact (@lem6978087 (term426 _128066 s) b). Qed.
Lemma lem6978089 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term425 _128066 s b) = (term428 _128066 s b).
Proof. exact (TRANS (@lem6978084 _128066 s b) (@lem6978088 _128066 s b)). Qed.
Lemma lem6978090 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term424 _128066 s b) = (term428 _128066 s b).
Proof. exact (TRANS (@lem6978078 _128066 s b) (@lem6978089 _128066 s b)). Qed.
Lemma lem6978091 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (term429 _128066 s f) = (term430 _128066 s f).
Proof. exact (MK_COMB (@lem6978049) (@lem6978066 _128066 s f)). Qed.
Lemma lem6978092 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term431 _128066 f s b).
Proof. exact (MK_COMB (@lem6978091 _128066 s f) (@lem6978090 _128066 s b)). Qed.
Lemma lem6978094 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978095 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6978094 nat (nat -> Prop) f x). Qed.
Lemma lem6978096 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) : (term430 _128066 s f) = (term432 _128066 s f).
Proof. exact (@lem6978095 Peano.lt (term421 _128066 s f)). Qed.
Lemma lem6978097 {_128066 : Type'} (s : _128066 -> Prop) (b : nat) : (term428 _128066 s b) = (term428 _128066 s b).
Proof. exact (eq_refl (term428 _128066 s b)). Qed.
Lemma lem6978098 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term431 _128066 f s b) = (term433 _128066 f s b).
Proof. exact (MK_COMB (@lem6978096 _128066 s f) (@lem6978097 _128066 s b)). Qed.
Lemma lem6978100 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978101 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6978100 nat Prop f x). Qed.
Lemma lem6978102 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term433 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (@lem6978101 (term432 _128066 s f) (term428 _128066 s b)). Qed.
Lemma lem6978103 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term431 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (TRANS (@lem6978098 _128066 f s b) (@lem6978102 _128066 f s b)). Qed.
Lemma lem6978104 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term39 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (TRANS (@lem6978092 _128066 f s b) (@lem6978103 _128066 f s b)). Qed.
Lemma lem6978105 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term76 _128066 f s b) = (term495 _128066 f s b).
Proof. exact (MK_COMB (@lem6978048) (@lem6978104 _128066 f s b)). Qed.
Lemma lem6978106 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem6978111 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978113 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (f x) = (@I (_128066 -> nat) f x).
Proof. exact (@lem6978111 _128066 nat f x). Qed.
Lemma lem6978114 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6978115 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (term435 _128066 f x) = (term436 _128066 f x).
Proof. exact (MK_COMB (@lem6978106) (@lem6978113 _128066 f x)). Qed.
Lemma lem6978116 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term71 _128066 f x b) = (term437 _128066 f x b).
Proof. exact (MK_COMB (@lem6978115 _128066 f x) (@lem6978114 b)). Qed.
Lemma lem6978118 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978119 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem6978118 nat (nat -> Prop) f x). Qed.
Lemma lem6978120 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) : (term436 _128066 f x) = (term438 _128066 f x).
Proof. exact (@lem6978119 Peano.lt (@I (_128066 -> nat) f x)). Qed.
Lemma lem6978121 (b : nat) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem6978122 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term437 _128066 f x b) = (term439 _128066 f x b).
Proof. exact (MK_COMB (@lem6978120 _128066 f x) (@lem6978121 b)). Qed.
Lemma lem6978124 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978125 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem6978124 nat Prop f x). Qed.
Lemma lem6978126 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term439 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (@lem6978125 (term438 _128066 f x) b). Qed.
Lemma lem6978127 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term437 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (TRANS (@lem6978122 _128066 f x b) (@lem6978126 _128066 f x b)). Qed.
Lemma lem6978128 {_128066 : Type'} (f : _128066 -> nat) (x : _128066) (b : nat) : (term71 _128066 f x b) = (term440 _128066 f x b).
Proof. exact (TRANS (@lem6978116 _128066 f x b) (@lem6978127 _128066 f x b)). Qed.
Lemma lem6978129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6978136 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978137 {_128066 : Type'} (f : type1364 _128066) (x : _128066) : (f x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978136 _128066 (type686 _128066) f x). Qed.
Lemma lem6978138 {_128066 : Type'} (x : _128066) : (@IN _128066 x) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x).
Proof. exact (@lem6978137 _128066 (@IN _128066) x). Qed.
Lemma lem6978139 {_128066 : Type'} (s : _128066 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6978140 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s).
Proof. exact (MK_COMB (@lem6978138 _128066 x) (@lem6978139 _128066 s)). Qed.
Lemma lem6978142 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978143 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978142 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6978144 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x s) = (term399 _128066 x s).
Proof. exact (@lem6978143 _128066 (@I (_128066 -> (_128066 -> Prop) -> Prop) (@IN _128066) x) s). Qed.
Lemma lem6978146 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (@IN _128066 x s) = (term399 _128066 x s).
Proof. exact (TRANS (@lem6978140 _128066 x s) (@lem6978144 _128066 x s)). Qed.
Lemma lem6978147 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term286 _128066 x s) = (term400 _128066 x s).
Proof. exact (MK_COMB (@lem6978129) (@lem6978146 _128066 x s)). Qed.
Lemma lem6978148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978149 {_128066 : Type'} (x : _128066) (s : _128066 -> Prop) : (term443 _128066 x s) = (term444 _128066 x s).
Proof. exact (MK_COMB (@lem6978148) (@lem6978147 _128066 x s)). Qed.
Lemma lem6978150 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term70 _128066 s f x b) = (term496 _128066 s f x b).
Proof. exact (MK_COMB (@lem6978149 _128066 x s) (@lem6978128 _128066 f x b)). Qed.
Lemma lem6978151 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term72 _128066 s f b) = (term497 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978150 _128066 s f x b)). Qed.
Lemma lem6978152 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978153 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term73 _128066 s f b) = (term498 _128066 s f b).
Proof. exact (MK_COMB (@lem6978152 _128066) (@lem6978151 _128066 s f b)). Qed.
Lemma lem6978162 {_128066 : Type'} (s : _128066 -> Prop) : (term60 _128066 s) = (term60 _128066 s).
Proof. exact (eq_refl (term60 _128066 s)). Qed.
Lemma lem6978163 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term74 _128066 s f b) = (term499 _128066 s f b).
Proof. exact (MK_COMB (@lem6978162 _128066 s) (@lem6978153 _128066 s f b)). Qed.
Lemma lem6978168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6978169 {_128066 : Type'} (f : type686 _128066) (x : _128066 -> Prop) : (f x) = (@I ((_128066 -> Prop) -> Prop) f x).
Proof. exact (@lem6978168 (_128066 -> Prop) Prop f x). Qed.
Lemma lem6978171 {_128066 : Type'} (s : _128066 -> Prop) : (@FINITE _128066 s) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s).
Proof. exact (@lem6978169 _128066 (@FINITE _128066) s). Qed.
Lemma lem6978172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6978173 {_128066 : Type'} (s : _128066 -> Prop) : (term48 _128066 s) = (term500 _128066 s).
Proof. exact (MK_COMB (@lem6978172) (@lem6978171 _128066 s)). Qed.
Lemma lem6978174 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term75 _128066 s f b) = (term501 _128066 s f b).
Proof. exact (MK_COMB (@lem6978173 _128066 s) (@lem6978163 _128066 s f b)). Qed.
Lemma lem6978175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6978176 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term78 _128066 s f b) = (term502 _128066 s f b).
Proof. exact (MK_COMB (@lem6978175) (@lem6978174 _128066 s f b)). Qed.
Lemma lem6978177 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term80 _128066 f s b) = (term503 _128066 f s b).
Proof. exact (MK_COMB (@lem6978176 _128066 s f b) (@lem6978105 _128066 f s b)). Qed.
Lemma lem6978178 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term503 _128066 f s b.
Proof. exact (EQ_MP (@lem6978177 _128066 f s b) (@lem6977465 _128066 f s b h1)). Qed.
Lemma lem6978180 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term501 _128066 s f b.
Proof. exact (proj1 (@lem6978178 _128066 f s b h1)). Qed.
Lemma lem6978181 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term499 _128066 s f b.
Proof. exact (proj2 (@lem6978180 _128066 f s b h1)). Qed.
Lemma lem6978183 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term498 _128066 s f b.
Proof. exact (proj2 (@lem6978181 _128066 f s b h1)). Qed.
Lemma lem6978186 {_128066 : Type'} (x : type684 _128066) (h1 : term384 _128066 x) : term418 _128066 x.
Proof. exact (proj1 (@lem6977585 _128066 x h1)). Qed.
Lemma lem6978194 (m : nat) (n : nat) : (term394 m n) = (term394 m n).
Proof. exact (eq_refl (term394 m n)). Qed.
Lemma lem6978195 (m : nat) : (term395 m) = (term395 m).
Proof. exact (fun_ext (fun n : nat => @lem6978194 m n)). Qed.
Lemma lem6978196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6978197 (m : nat) : (term396 m) = (term396 m).
Proof. exact (MK_COMB (@lem6978196) (@lem6978195 m)). Qed.
Lemma lem6978198 : term397 = term397.
Proof. exact (fun_ext (fun m : nat => @lem6978197 m)). Qed.
Lemma lem6978199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6978201 : term398 = term398.
Proof. exact (MK_COMB (@lem6978199) (@lem6978198)). Qed.
Lemma lem6978202 (h1 : term38) : term398.
Proof. exact (EQ_MP (@lem6978201) (@lem6977511 h1)). Qed.
Lemma lem6978346 {A : Type'} (P : Prop) (Q : A -> Prop) : (term504 A P Q) = (term505 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6978347 {_128066 : Type'} (P : Prop) (Q : _128066 -> Prop) : (term504 _128066 P Q) = (term505 _128066 P Q).
Proof. exact (@lem6978346 _128066 P Q). Qed.
Lemma lem6978348 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term506 _128066 x'' s f b) = (term507 _128066 x'' s f b).
Proof. exact (@lem6978347 _128066 (term473 _128066 x'' s f b) (term446 _128066 s f b)). Qed.
Lemma lem6978349 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term508 _128066 s f b x) = (term445 _128066 s f x b).
Proof. exact (eq_refl (term508 _128066 s f b x)). Qed.
Lemma lem6978350 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term509 _128066 s f b) = (term446 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978349 _128066 s f x b)). Qed.
Lemma lem6978351 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978352 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term510 _128066 s f b) = (term447 _128066 s f b).
Proof. exact (MK_COMB (@lem6978351 _128066) (@lem6978350 _128066 s f b)). Qed.
Lemma lem6978353 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term475 _128066 x'' s f b) = (term475 _128066 x'' s f b).
Proof. exact (eq_refl (term475 _128066 x'' s f b)). Qed.
Lemma lem6978354 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term506 _128066 x'' s f b) = (term477 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978353 _128066 x'' s f b) (@lem6978352 _128066 s f b)). Qed.
Lemma lem6978355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6978356 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term511 _128066 x'' s f b) = (term512 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978355) (@lem6978354 _128066 x'' s f b)). Qed.
Lemma lem6978357 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term508 _128066 s f b x) = (term445 _128066 s f x b).
Proof. exact (eq_refl (term508 _128066 s f b x)). Qed.
Lemma lem6978358 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term475 _128066 x'' s f b) = (term475 _128066 x'' s f b).
Proof. exact (eq_refl (term475 _128066 x'' s f b)). Qed.
Lemma lem6978359 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term513 _128066 x'' s f b x) = (term514 _128066 x'' s f x b).
Proof. exact (MK_COMB (@lem6978358 _128066 x'' s f b) (@lem6978357 _128066 s f x b)). Qed.
Lemma lem6978360 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term515 _128066 x'' s f b) = (term516 _128066 x'' s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978359 _128066 x'' s f x b)). Qed.
Lemma lem6978361 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978362 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term507 _128066 x'' s f b) = (term517 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978361 _128066) (@lem6978360 _128066 x'' s f b)). Qed.
Lemma lem6978363 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : ((term506 _128066 x'' s f b) = (term507 _128066 x'' s f b)) = ((term477 _128066 x'' s f b) = (term517 _128066 x'' s f b)).
Proof. exact (MK_COMB (@lem6978356 _128066 x'' s f b) (@lem6978362 _128066 x'' s f b)). Qed.
Lemma lem6978364 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term477 _128066 x'' s f b) = (term517 _128066 x'' s f b).
Proof. exact (EQ_MP (@lem6978363 _128066 x'' s f b) (@lem6978348 _128066 x'' s f b)). Qed.
Lemma lem6978365 {_128066 : Type'} (s : _128066 -> Prop) : (term479 _128066 s) = (term479 _128066 s).
Proof. exact (eq_refl (term479 _128066 s)). Qed.
Lemma lem6978366 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term481 _128066 x'' s f b) = (term518 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978365 _128066 s) (@lem6978364 _128066 x'' s f b)). Qed.
Lemma lem6978368 {A : Type'} (P : Prop) (Q : A -> Prop) : (term504 A P Q) = (term505 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem6978369 {_128066 : Type'} (P : Prop) (Q : _128066 -> Prop) : (term504 _128066 P Q) = (term505 _128066 P Q).
Proof. exact (@lem6978368 _128066 P Q). Qed.
Lemma lem6978370 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term519 _128066 x'' s f b) = (term520 _128066 x'' s f b).
Proof. exact (@lem6978369 _128066 (term478 _128066 s) (term516 _128066 x'' s f b)). Qed.
Lemma lem6978371 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term521 _128066 x'' s f b x) = (term514 _128066 x'' s f x b).
Proof. exact (eq_refl (term521 _128066 x'' s f b x)). Qed.
Lemma lem6978372 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term522 _128066 x'' s f b) = (term516 _128066 x'' s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978371 _128066 x'' s f x b)). Qed.
Lemma lem6978373 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978374 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term523 _128066 x'' s f b) = (term517 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978373 _128066) (@lem6978372 _128066 x'' s f b)). Qed.
Lemma lem6978375 {_128066 : Type'} (s : _128066 -> Prop) : (term479 _128066 s) = (term479 _128066 s).
Proof. exact (eq_refl (term479 _128066 s)). Qed.
Lemma lem6978376 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term519 _128066 x'' s f b) = (term518 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978375 _128066 s) (@lem6978374 _128066 x'' s f b)). Qed.
Lemma lem6978377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6978378 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term524 _128066 x'' s f b) = (term525 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978377) (@lem6978376 _128066 x'' s f b)). Qed.
Lemma lem6978379 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term521 _128066 x'' s f b x) = (term514 _128066 x'' s f x b).
Proof. exact (eq_refl (term521 _128066 x'' s f b x)). Qed.
Lemma lem6978380 {_128066 : Type'} (s : _128066 -> Prop) : (term479 _128066 s) = (term479 _128066 s).
Proof. exact (eq_refl (term479 _128066 s)). Qed.
Lemma lem6978381 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term526 _128066 x'' s f b x) = (term527 _128066 x'' s f x b).
Proof. exact (MK_COMB (@lem6978380 _128066 s) (@lem6978379 _128066 x'' s f x b)). Qed.
Lemma lem6978382 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term528 _128066 x'' s f b) = (term529 _128066 x'' s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978381 _128066 x'' s f x b)). Qed.
Lemma lem6978383 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978384 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term520 _128066 x'' s f b) = (term530 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978383 _128066) (@lem6978382 _128066 x'' s f b)). Qed.
Lemma lem6978385 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : ((term519 _128066 x'' s f b) = (term520 _128066 x'' s f b)) = ((term518 _128066 x'' s f b) = (term530 _128066 x'' s f b)).
Proof. exact (MK_COMB (@lem6978378 _128066 x'' s f b) (@lem6978384 _128066 x'' s f b)). Qed.
Lemma lem6978386 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term518 _128066 x'' s f b) = (term530 _128066 x'' s f b).
Proof. exact (EQ_MP (@lem6978385 _128066 x'' s f b) (@lem6978370 _128066 x'' s f b)). Qed.
Lemma lem6978387 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term481 _128066 x'' s f b) = (term530 _128066 x'' s f b).
Proof. exact (TRANS (@lem6978366 _128066 x'' s f b) (@lem6978386 _128066 x'' s f b)). Qed.
Lemma lem6978388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978389 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term483 _128066 x'' s f b) = (term531 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978388) (@lem6978387 _128066 x'' s f b)). Qed.
Lemma lem6978390 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term434 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (eq_refl (term434 _128066 f s b)). Qed.
Lemma lem6978391 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term485 _128066 x'' f s b) = (term532 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978389 _128066 x'' s f b) (@lem6978390 _128066 f s b)). Qed.
Lemma lem6978393 {A : Type'} (P : A -> Prop) (Q : Prop) : (term533 A P Q) = (term534 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem6978394 {_128066 : Type'} (P : _128066 -> Prop) (Q : Prop) : (term533 _128066 P Q) = (term534 _128066 P Q).
Proof. exact (@lem6978393 _128066 P Q). Qed.
Lemma lem6978395 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term535 _128066 x'' f s b) = (term536 _128066 x'' f s b).
Proof. exact (@lem6978394 _128066 (term529 _128066 x'' s f b) (term434 _128066 f s b)). Qed.
Lemma lem6978396 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term537 _128066 x'' s f b x) = (term527 _128066 x'' s f x b).
Proof. exact (eq_refl (term537 _128066 x'' s f b x)). Qed.
Lemma lem6978397 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term538 _128066 x'' s f b) = (term529 _128066 x'' s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978396 _128066 x'' s f x b)). Qed.
Lemma lem6978398 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978399 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term539 _128066 x'' s f b) = (term530 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978398 _128066) (@lem6978397 _128066 x'' s f b)). Qed.
Lemma lem6978400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978401 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term540 _128066 x'' s f b) = (term531 _128066 x'' s f b).
Proof. exact (MK_COMB (@lem6978400) (@lem6978399 _128066 x'' s f b)). Qed.
Lemma lem6978402 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term434 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (eq_refl (term434 _128066 f s b)). Qed.
Lemma lem6978403 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term535 _128066 x'' f s b) = (term532 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978401 _128066 x'' s f b) (@lem6978402 _128066 f s b)). Qed.
Lemma lem6978404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6978405 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term541 _128066 x'' f s b) = (term542 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978404) (@lem6978403 _128066 x'' f s b)). Qed.
Lemma lem6978406 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term537 _128066 x'' s f b x) = (term527 _128066 x'' s f x b).
Proof. exact (eq_refl (term537 _128066 x'' s f b x)). Qed.
Lemma lem6978407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978408 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term543 _128066 x'' s f b x) = (term544 _128066 x'' s f x b).
Proof. exact (MK_COMB (@lem6978407) (@lem6978406 _128066 x'' s f x b)). Qed.
Lemma lem6978409 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term434 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (eq_refl (term434 _128066 f s b)). Qed.
Lemma lem6978410 {_128066 : Type'} (x'' : type642 _128066) (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term545 _128066 x'' x f s b) = (term546 _128066 x'' x f s b).
Proof. exact (MK_COMB (@lem6978408 _128066 x'' s f x b) (@lem6978409 _128066 f s b)). Qed.
Lemma lem6978411 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term547 _128066 x'' f s b) = (term548 _128066 x'' f s b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978410 _128066 x'' x f s b)). Qed.
Lemma lem6978412 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978413 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term536 _128066 x'' f s b) = (term549 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978412 _128066) (@lem6978411 _128066 x'' f s b)). Qed.
Lemma lem6978414 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : ((term535 _128066 x'' f s b) = (term536 _128066 x'' f s b)) = ((term532 _128066 x'' f s b) = (term549 _128066 x'' f s b)).
Proof. exact (MK_COMB (@lem6978405 _128066 x'' f s b) (@lem6978413 _128066 x'' f s b)). Qed.
Lemma lem6978415 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term532 _128066 x'' f s b) = (term549 _128066 x'' f s b).
Proof. exact (EQ_MP (@lem6978414 _128066 x'' f s b) (@lem6978395 _128066 x'' f s b)). Qed.
Lemma lem6978416 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term485 _128066 x'' f s b) = (term549 _128066 x'' f s b).
Proof. exact (TRANS (@lem6978391 _128066 x'' f s b) (@lem6978415 _128066 x'' f s b)). Qed.
Lemma lem6978417 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term487 _128066 x'' f s) = (term550 _128066 x'' f s).
Proof. exact (fun_ext (fun b : nat => @lem6978416 _128066 x'' f s b)). Qed.
Lemma lem6978418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6978419 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term489 _128066 x'' f s) = (term551 _128066 x'' f s).
Proof. exact (MK_COMB (@lem6978418) (@lem6978417 _128066 x'' f s)). Qed.
Lemma lem6978420 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term491 _128066 x'' s) = (term552 _128066 x'' s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6978419 _128066 x'' f s)). Qed.
Lemma lem6978421 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6978422 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term492 _128066 x'' s) = (term553 _128066 x'' s).
Proof. exact (MK_COMB (@lem6978421 _128066) (@lem6978420 _128066 x'' s)). Qed.
Lemma lem6978423 {_128066 : Type'} (x'' : type642 _128066) : (term493 _128066 x'') = (term554 _128066 x'').
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6978422 _128066 x'' s)). Qed.
Lemma lem6978424 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6978425 {_128066 : Type'} (x'' : type642 _128066) : (term494 _128066 x'') = (term555 _128066 x'').
Proof. exact (MK_COMB (@lem6978424 _128066) (@lem6978423 _128066 x'')). Qed.
Lemma lem6978426 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term434 _128066 f s b) = (term434 _128066 f s b).
Proof. exact (eq_refl (term434 _128066 f s b)). Qed.
Lemma lem6978449 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term514 _128066 x'' s f x b) = (term556 _128066 x'' s f x b).
Proof. exact (@lem19699 (term469 _128066 x'' f b s) (term462 _128066 x'' s f b) (term445 _128066 s f x b)). Qed.
Lemma lem6978452 {_128066 : Type'} (s : _128066 -> Prop) : (term479 _128066 s) = (term479 _128066 s).
Proof. exact (eq_refl (term479 _128066 s)). Qed.
Lemma lem6978453 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term527 _128066 x'' s f x b) = (term557 _128066 x'' s f x b).
Proof. exact (MK_COMB (@lem6978452 _128066 s) (@lem6978449 _128066 x'' s f x b)). Qed.
Lemma lem6978460 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term557 _128066 x'' s f x b) = (term558 _128066 x'' s f x b).
Proof. exact (@lem19490 (term559 _128066 x'' s f x b) (term478 _128066 s) (term560 _128066 x'' s f x b)). Qed.
Lemma lem6978461 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term527 _128066 x'' s f x b) = (term558 _128066 x'' s f x b).
Proof. exact (TRANS (@lem6978453 _128066 x'' s f x b) (@lem6978460 _128066 x'' s f x b)). Qed.
Lemma lem6978462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6978463 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term544 _128066 x'' s f x b) = (term561 _128066 x'' s f x b).
Proof. exact (MK_COMB (@lem6978462) (@lem6978461 _128066 x'' s f x b)). Qed.
Lemma lem6978464 {_128066 : Type'} (x'' : type642 _128066) (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term546 _128066 x'' x f s b) = (term562 _128066 x'' x f s b).
Proof. exact (MK_COMB (@lem6978463 _128066 x'' s f x b) (@lem6978426 _128066 f s b)). Qed.
Lemma lem6978471 {_128066 : Type'} (x'' : type642 _128066) (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term562 _128066 x'' x f s b) = (term563 _128066 x'' x f s b).
Proof. exact (@lem19699 (term564 _128066 x'' s f x b) (term565 _128066 x'' s f x b) (term434 _128066 f s b)). Qed.
Lemma lem6978472 {_128066 : Type'} (x'' : type642 _128066) (x : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term546 _128066 x'' x f s b) = (term563 _128066 x'' x f s b).
Proof. exact (TRANS (@lem6978464 _128066 x'' x f s b) (@lem6978471 _128066 x'' x f s b)). Qed.
Lemma lem6978473 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term548 _128066 x'' f s b) = (term566 _128066 x'' f s b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978472 _128066 x'' x f s b)). Qed.
Lemma lem6978474 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978475 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term549 _128066 x'' f s b) = (term567 _128066 x'' f s b).
Proof. exact (MK_COMB (@lem6978474 _128066) (@lem6978473 _128066 x'' f s b)). Qed.
Lemma lem6978476 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term550 _128066 x'' f s) = (term568 _128066 x'' f s).
Proof. exact (fun_ext (fun b : nat => @lem6978475 _128066 x'' f s b)). Qed.
Lemma lem6978477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6978478 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) : (term551 _128066 x'' f s) = (term569 _128066 x'' f s).
Proof. exact (MK_COMB (@lem6978477) (@lem6978476 _128066 x'' f s)). Qed.
Lemma lem6978479 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term552 _128066 x'' s) = (term570 _128066 x'' s).
Proof. exact (fun_ext (fun f : _128066 -> nat => @lem6978478 _128066 x'' f s)). Qed.
Lemma lem6978480 {_128066 : Type'} : (@all (_128066 -> nat)) = (@all (_128066 -> nat)).
Proof. exact (eq_refl (@all (_128066 -> nat))). Qed.
Lemma lem6978481 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) : (term553 _128066 x'' s) = (term571 _128066 x'' s).
Proof. exact (MK_COMB (@lem6978480 _128066) (@lem6978479 _128066 x'' s)). Qed.
Lemma lem6978482 {_128066 : Type'} (x'' : type642 _128066) : (term554 _128066 x'') = (term572 _128066 x'').
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6978481 _128066 x'' s)). Qed.
Lemma lem6978483 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6978484 {_128066 : Type'} (x'' : type642 _128066) : (term555 _128066 x'') = (term573 _128066 x'').
Proof. exact (MK_COMB (@lem6978483 _128066) (@lem6978482 _128066 x'')). Qed.
Lemma lem6978485 {_128066 : Type'} (x'' : type642 _128066) : (term494 _128066 x'') = (term573 _128066 x'').
Proof. exact (TRANS (@lem6978425 _128066 x'') (@lem6978484 _128066 x'')). Qed.
Lemma lem6978486 {_128066 : Type'} (x'' : type642 _128066) (h1 : term273 _128066 x'') : term573 _128066 x''.
Proof. exact (EQ_MP (@lem6978485 _128066 x'') (@lem6978047 _128066 x'' h1)). Qed.
Lemma lem6978506 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (x : _128066) (b : nat) : (term496 _128066 s f x b) = (term496 _128066 s f x b).
Proof. exact (eq_refl (term496 _128066 s f x b)). Qed.
Lemma lem6978507 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term497 _128066 s f b) = (term497 _128066 s f b).
Proof. exact (fun_ext (fun x : _128066 => @lem6978506 _128066 s f x b)). Qed.
Lemma lem6978508 {_128066 : Type'} : (@all _128066) = (@all _128066).
Proof. exact (eq_refl (@all _128066)). Qed.
Lemma lem6978510 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term498 _128066 s f b) = (term498 _128066 s f b).
Proof. exact (MK_COMB (@lem6978508 _128066) (@lem6978507 _128066 s f b)). Qed.
Lemma lem6978511 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term498 _128066 s f b.
Proof. exact (EQ_MP (@lem6978510 _128066 s f b) (@lem6978183 _128066 f s b h1)). Qed.
Lemma lem6978519 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term416 _128066 x s) = (term416 _128066 x s).
Proof. exact (eq_refl (term416 _128066 x s)). Qed.
Lemma lem6978520 {_128066 : Type'} (x : type684 _128066) : (term417 _128066 x) = (term417 _128066 x).
Proof. exact (fun_ext (fun s : _128066 -> Prop => @lem6978519 _128066 x s)). Qed.
Lemma lem6978521 {_128066 : Type'} : (@all (_128066 -> Prop)) = (@all (_128066 -> Prop)).
Proof. exact (eq_refl (@all (_128066 -> Prop))). Qed.
Lemma lem6978523 {_128066 : Type'} (x : type684 _128066) : (term418 _128066 x) = (term418 _128066 x).
Proof. exact (MK_COMB (@lem6978521 _128066) (@lem6978520 _128066 x)). Qed.
Lemma lem6978524 {_128066 : Type'} (x : type684 _128066) (h1 : term384 _128066 x) : term418 _128066 x.
Proof. exact (EQ_MP (@lem6978523 _128066 x) (@lem6978186 _128066 x h1)). Qed.
Lemma lem6978567 (_92880 : nat) (h1 : term38) : term574 _92880.
Proof. exact (@lem6978202 h1 _92880). Qed.
Lemma lem6978568 (_92880 : nat) : (term574 _92880) = (term396 _92880).
Proof. exact (eq_refl (term574 _92880)). Qed.
Lemma lem6978569 (_92880 : nat) (h1 : term38) : term396 _92880.
Proof. exact (EQ_MP (@lem6978568 _92880) (@lem6978567 _92880 h1)). Qed.
Lemma lem6978570 (_92880 : nat) (_92881 : nat) (h1 : term38) : term575 _92880 _92881.
Proof. exact (@lem6978569 _92880 h1 _92881). Qed.
Lemma lem6978571 (_92880 : nat) (_92881 : nat) : (term575 _92880 _92881) = (term394 _92880 _92881).
Proof. exact (eq_refl (term575 _92880 _92881)). Qed.
Lemma lem6978585 {_128066 : Type'} (_92886 : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term576 _128066 x'' _92886.
Proof. exact (@lem6978486 _128066 x'' h1 _92886). Qed.
Lemma lem6978586 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) : (term576 _128066 x'' _92886) = (term571 _128066 x'' _92886).
Proof. exact (eq_refl (term576 _128066 x'' _92886)). Qed.
Lemma lem6978587 {_128066 : Type'} (_92886 : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term571 _128066 x'' _92886.
Proof. exact (EQ_MP (@lem6978586 _128066 x'' _92886) (@lem6978585 _128066 _92886 x'' h1)). Qed.
Lemma lem6978588 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term577 _128066 x'' _92886 _92887.
Proof. exact (@lem6978587 _128066 _92886 x'' h1 _92887). Qed.
Lemma lem6978589 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) : (term577 _128066 x'' _92886 _92887) = (term569 _128066 x'' _92887 _92886).
Proof. exact (eq_refl (term577 _128066 x'' _92886 _92887)). Qed.
Lemma lem6978590 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term569 _128066 x'' _92887 _92886.
Proof. exact (EQ_MP (@lem6978589 _128066 x'' _92887 _92886) (@lem6978588 _128066 _92886 _92887 x'' h1)). Qed.
Lemma lem6978591 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term578 _128066 x'' _92887 _92886 _92888.
Proof. exact (@lem6978590 _128066 _92887 _92886 x'' h1 _92888). Qed.
Lemma lem6978592 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term578 _128066 x'' _92887 _92886 _92888) = (term567 _128066 x'' _92887 _92886 _92888).
Proof. exact (eq_refl (term578 _128066 x'' _92887 _92886 _92888)). Qed.
Lemma lem6978593 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term567 _128066 x'' _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6978592 _128066 x'' _92887 _92886 _92888) (@lem6978591 _128066 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6978594 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (_92889 : _128066) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term579 _128066 x'' _92887 _92886 _92888 _92889.
Proof. exact (@lem6978593 _128066 _92887 _92886 _92888 x'' h1 _92889). Qed.
Lemma lem6978595 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term579 _128066 x'' _92887 _92886 _92888 _92889) = (term563 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (eq_refl (term579 _128066 x'' _92887 _92886 _92888 _92889)). Qed.
Lemma lem6978596 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term563 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6978595 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978594 _128066 _92887 _92886 _92888 _92889 x'' h1)). Qed.
Lemma lem6978597 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term580 _128066 s f b _92890.
Proof. exact (@lem6978511 _128066 f s b h1 _92890). Qed.
Lemma lem6978598 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (_92890 : _128066) (b : nat) : (term580 _128066 s f b _92890) = (term496 _128066 s f _92890 b).
Proof. exact (eq_refl (term580 _128066 s f b _92890)). Qed.
Lemma lem6978600 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term581 _128066 x _92891.
Proof. exact (@lem6978524 _128066 x h1 _92891). Qed.
Lemma lem6978601 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term581 _128066 x _92891) = (term416 _128066 x _92891).
Proof. exact (eq_refl (term581 _128066 x _92891)). Qed.
Lemma lem6978609 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term582 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (proj2 (@lem6978596 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6978610 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term583 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (proj1 (@lem6978596 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6978618 (_92880 : nat) (_92881 : nat) (h1 : term38) : term394 _92880 _92881.
Proof. exact (EQ_MP (@lem6978571 _92880 _92881) (@lem6978570 _92880 _92881 h1)). Qed.
Lemma lem6978624 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term29 _128066 s.
Proof. exact (proj1 (@lem6978181 _128066 f s b h1)). Qed.
Lemma lem6978630 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term496 _128066 s f _92890 b.
Proof. exact (EQ_MP (@lem6978598 _128066 s f _92890 b) (@lem6978597 _128066 _92890 f s b h1)). Qed.
Lemma lem6978636 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term416 _128066 x _92891.
Proof. exact (EQ_MP (@lem6978601 _128066 x _92891) (@lem6978600 _128066 _92891 x h1)). Qed.
Lemma lem6978646 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term583 _128066 x'' _92889 _92887 _92886 _92888) = (term584 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term478 _128066 _92886) (term559 _128066 x'' _92886 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978647 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term585 _128066 x'' _92889 _92887 _92886 _92888) = (term586 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term469 _128066 x'' _92887 _92888 _92886) (term445 _128066 _92886 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978654 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term587 _128066 _92889 _92887 _92886 _92888) = (term588 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term400 _128066 _92889 _92886) (term442 _128066 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978655 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term589 _128066 x'' _92887 _92888 _92886) = (term589 _128066 x'' _92887 _92888 _92886).
Proof. exact (eq_refl (term589 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6978658 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term586 _128066 x'' _92889 _92887 _92886 _92888) = (term590 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6978655 _128066 x'' _92887 _92888 _92886) (@lem6978654 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978659 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term585 _128066 x'' _92889 _92887 _92886 _92888) = (term590 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6978647 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978658 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978660 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6978663 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term584 _128066 x'' _92889 _92887 _92886 _92888) = (term591 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6978660 _128066 _92886) (@lem6978659 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978665 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term583 _128066 x'' _92889 _92887 _92886 _92888) = (term591 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6978646 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978663 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978666 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term591 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6978665 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978610 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6978670 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term582 _128066 x'' _92889 _92887 _92886 _92888) = (term592 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term478 _128066 _92886) (term560 _128066 x'' _92886 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978671 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term593 _128066 x'' _92889 _92887 _92886 _92888) = (term594 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term462 _128066 x'' _92886 _92887 _92888) (term445 _128066 _92886 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978678 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term587 _128066 _92889 _92887 _92886 _92888) = (term588 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6975637 (term400 _128066 _92889 _92886) (term442 _128066 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6978679 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term595 _128066 x'' _92886 _92887 _92888) = (term595 _128066 x'' _92886 _92887 _92888).
Proof. exact (eq_refl (term595 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6978682 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term594 _128066 x'' _92889 _92887 _92886 _92888) = (term596 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6978679 _128066 x'' _92886 _92887 _92888) (@lem6978678 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978683 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term593 _128066 x'' _92889 _92887 _92886 _92888) = (term596 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6978671 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978682 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978684 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6978687 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term592 _128066 x'' _92889 _92887 _92886 _92888) = (term597 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6978684 _128066 _92886) (@lem6978683 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978689 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term582 _128066 x'' _92889 _92887 _92886 _92888) = (term597 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6978670 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978687 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6978690 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term597 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6978689 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978609 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6979153 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : @I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s.
Proof. exact (proj1 (@lem6978180 _128066 f s b h1)). Qed.
Lemma lem6979154 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term598 _128066 s.
Proof. exact (fun h0 : term478 _128066 s => @lem6979153 _128066 f s b h1). Qed.
Lemma lem6979156 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979157 {_128066 : Type'} (s : _128066 -> Prop) : (term598 _128066 s) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s).
Proof. exact (@lem6979156 (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s)). Qed.
Lemma lem6979158 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : @I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s.
Proof. exact (EQ_MP (@lem6979157 _128066 s) (@lem6979154 _128066 f s b h1)). Qed.
Lemma lem6979160 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : @I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s.
Proof. exact (proj1 (@lem6978180 _128066 f s b h1)). Qed.
Lemma lem6979161 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term598 _128066 s.
Proof. exact (fun h0 : term478 _128066 s => @lem6979160 _128066 f s b h1). Qed.
Lemma lem6979163 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979164 {_128066 : Type'} (s : _128066 -> Prop) : (term598 _128066 s) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s).
Proof. exact (@lem6979163 (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s)). Qed.
Lemma lem6979165 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : @I ((_128066 -> Prop) -> Prop) (@FINITE _128066) s.
Proof. exact (EQ_MP (@lem6979164 _128066 s) (@lem6979161 _128066 f s b h1)). Qed.
Lemma lem6979168 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (h1). Qed.
Lemma lem6979169 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term600 _128066 s.
Proof. exact (fun h0 : s = (@EMPTY _128066) => @lem6979168 _128066 s h1). Qed.
Lemma lem6979171 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6979172 {_128066 : Type'} (s : _128066 -> Prop) : (term600 _128066 s) = (term29 _128066 s).
Proof. exact (@lem6979171 (s = (@EMPTY _128066))). Qed.
Lemma lem6979173 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (EQ_MP (@lem6979172 _128066 s) (@lem6979169 _128066 s h1)). Qed.
Lemma lem6979175 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6979178 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term416 _128066 x _92891) = (term603 _128066 x _92891).
Proof. exact (@lem6979175 (_92891 = (@EMPTY _128066)) (term413 _128066 x _92891)). Qed.
Lemma lem6979181 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (EQ_MP (@lem6979178 _128066 x _92891) (@lem6978636 _128066 _92891 x h1)). Qed.
Lemma lem6979182 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (@lem6979181 _128066 _92891 x h1). Qed.
Lemma lem6979183 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x s.
Proof. exact (@lem6979182 _128066 s x h1). Qed.
Lemma lem6979186 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (@lem6979183 _128066 s x h2 (@lem6979173 _128066 s h1)). Qed.
Lemma lem6979187 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term604 _128066 x s.
Proof. exact (fun h0 : term605 _128066 x s => @lem6979186 _128066 s x h1 h2). Qed.
Lemma lem6979189 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979190 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term604 _128066 x s) = (term413 _128066 x s).
Proof. exact (@lem6979189 (term413 _128066 x s)). Qed.
Lemma lem6979191 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (EQ_MP (@lem6979190 _128066 x s) (@lem6979187 _128066 s x h1 h2)). Qed.
Lemma lem6979194 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (h1). Qed.
Lemma lem6979195 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term600 _128066 s.
Proof. exact (fun h0 : s = (@EMPTY _128066) => @lem6979194 _128066 s h1). Qed.
Lemma lem6979197 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6979198 {_128066 : Type'} (s : _128066 -> Prop) : (term600 _128066 s) = (term29 _128066 s).
Proof. exact (@lem6979197 (s = (@EMPTY _128066))). Qed.
Lemma lem6979199 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (EQ_MP (@lem6979198 _128066 s) (@lem6979195 _128066 s h1)). Qed.
Lemma lem6979201 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (EQ_MP (@lem6979178 _128066 x _92891) (@lem6978636 _128066 _92891 x h1)). Qed.
Lemma lem6979202 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (@lem6979201 _128066 _92891 x h1). Qed.
Lemma lem6979203 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x s.
Proof. exact (@lem6979202 _128066 s x h1). Qed.
Lemma lem6979206 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (@lem6979203 _128066 s x h2 (@lem6979199 _128066 s h1)). Qed.
Lemma lem6979207 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term604 _128066 x s.
Proof. exact (fun h0 : term605 _128066 x s => @lem6979206 _128066 s x h1 h2). Qed.
Lemma lem6979209 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979210 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term604 _128066 x s) = (term413 _128066 x s).
Proof. exact (@lem6979209 (term413 _128066 x s)). Qed.
Lemma lem6979211 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (EQ_MP (@lem6979210 _128066 x s) (@lem6979207 _128066 s x h1 h2)). Qed.
Lemma lem6979217 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979218 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : (term496 _128066 s f _92890 b) = (term606 _128066 f b _92890 s).
Proof. exact (@lem6979217 (term440 _128066 f _92890 b) (term400 _128066 _92890 s)). Qed.
Lemma lem6979224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6979225 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : (term607 _128066 s f _92890 b) = (term608 _128066 f b _92890 s).
Proof. exact (MK_COMB (@lem6979224) (@lem6979218 _128066 f b _92890 s)). Qed.
Lemma lem6979231 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : (term606 _128066 f b _92890 s) = (term606 _128066 f b _92890 s).
Proof. exact (eq_refl (term606 _128066 f b _92890 s)). Qed.
Lemma lem6979232 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : ((term496 _128066 s f _92890 b) = (term606 _128066 f b _92890 s)) = ((term606 _128066 f b _92890 s) = (term606 _128066 f b _92890 s)).
Proof. exact (MK_COMB (@lem6979225 _128066 f b _92890 s) (@lem6979231 _128066 f b _92890 s)). Qed.
Lemma lem6979234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6979235 (x : Prop) : (x = x) = True.
Proof. exact (@lem6979234 Prop x). Qed.
Lemma lem6979236 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : ((term606 _128066 f b _92890 s) = (term606 _128066 f b _92890 s)) = True.
Proof. exact (@lem6979235 (term606 _128066 f b _92890 s)). Qed.
Lemma lem6979237 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : ((term496 _128066 s f _92890 b) = (term606 _128066 f b _92890 s)) = True.
Proof. exact (TRANS (@lem6979232 _128066 f b _92890 s) (@lem6979236 _128066 f b _92890 s)). Qed.
Lemma lem6979238 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : True = ((term496 _128066 s f _92890 b) = (term606 _128066 f b _92890 s)).
Proof. exact (SYM (@lem6979237 _128066 f b _92890 s)). Qed.
Lemma lem6979239 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : (term496 _128066 s f _92890 b) = (term606 _128066 f b _92890 s).
Proof. exact (EQ_MP (@lem6979238 _128066 f b _92890 s) (@lem0)). Qed.
Lemma lem6979240 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term606 _128066 f b _92890 s.
Proof. exact (EQ_MP (@lem6979239 _128066 f b _92890 s) (@lem6978630 _128066 _92890 f s b h1)). Qed.
Lemma lem6979242 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6979243 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (_92890 : _128066) (b : nat) : (term606 _128066 f b _92890 s) = (term609 _128066 s f _92890 b).
Proof. exact (@lem6979242 (term400 _128066 _92890 s) (term440 _128066 f _92890 b)). Qed.
Lemma lem6979245 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979246 {_128066 : Type'} (_92890 : _128066) (s : _128066 -> Prop) : (term611 _128066 _92890 s) = (term399 _128066 _92890 s).
Proof. exact (@lem6979245 (term399 _128066 _92890 s)). Qed.
Lemma lem6979247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6979248 {_128066 : Type'} (_92890 : _128066) (s : _128066 -> Prop) : (term612 _128066 _92890 s) = (term613 _128066 _92890 s).
Proof. exact (MK_COMB (@lem6979247) (@lem6979246 _128066 _92890 s)). Qed.
Lemma lem6979249 {_128066 : Type'} (f : _128066 -> nat) (_92890 : _128066) (b : nat) : (term440 _128066 f _92890 b) = (term440 _128066 f _92890 b).
Proof. exact (eq_refl (term440 _128066 f _92890 b)). Qed.
Lemma lem6979250 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (_92890 : _128066) (b : nat) : (term609 _128066 s f _92890 b) = (term614 _128066 s f _92890 b).
Proof. exact (MK_COMB (@lem6979248 _128066 _92890 s) (@lem6979249 _128066 f _92890 b)). Qed.
Lemma lem6979251 {_128066 : Type'} (s : _128066 -> Prop) (f : _128066 -> nat) (_92890 : _128066) (b : nat) : (term606 _128066 f b _92890 s) = (term614 _128066 s f _92890 b).
Proof. exact (TRANS (@lem6979243 _128066 s f _92890 b) (@lem6979250 _128066 s f _92890 b)). Qed.
Lemma lem6979254 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term614 _128066 s f _92890 b.
Proof. exact (EQ_MP (@lem6979251 _128066 s f _92890 b) (@lem6979240 _128066 _92890 f s b h1)). Qed.
Lemma lem6979255 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term614 _128066 s f _92890 b.
Proof. exact (@lem6979254 _128066 _92890 f s b h1). Qed.
Lemma lem6979256 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term615 _128066 f x s b.
Proof. exact (@lem6979255 _128066 (@I ((_128066 -> Prop) -> _128066) x s) f s b h1). Qed.
Lemma lem6979259 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term616 _128066 f x s b.
Proof. exact (@lem6979256 _128066 x f s b h3 (@lem6979211 _128066 s x h1 h2)). Qed.
Lemma lem6979260 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term617 _128066 f x s b.
Proof. exact (fun h0 : term618 _128066 f x s b => @lem6979259 _128066 x f s b h1 h2 h3). Qed.
Lemma lem6979262 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979263 {_128066 : Type'} (f : _128066 -> nat) (x : type684 _128066) (s : _128066 -> Prop) (b : nat) : (term617 _128066 f x s b) = (term616 _128066 f x s b).
Proof. exact (@lem6979262 (term616 _128066 f x s b)). Qed.
Lemma lem6979264 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term616 _128066 f x s b.
Proof. exact (EQ_MP (@lem6979263 _128066 f x s b) (@lem6979260 _128066 x f s b h1 h2 h3)). Qed.
Lemma lem6979266 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term495 _128066 f s b.
Proof. exact (proj2 (@lem6978178 _128066 f s b h1)). Qed.
Lemma lem6979267 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term619 _128066 f s b.
Proof. exact (fun h0 : term434 _128066 f s b => @lem6979266 _128066 f s b h1). Qed.
Lemma lem6979269 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6979270 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term619 _128066 f s b) = (term495 _128066 f s b).
Proof. exact (@lem6979269 (term434 _128066 f s b)). Qed.
Lemma lem6979271 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term495 _128066 f s b.
Proof. exact (EQ_MP (@lem6979270 _128066 f s b) (@lem6979267 _128066 f s b h1)). Qed.
Lemma lem6979277 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979278 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term591 _128066 x'' _92889 _92887 _92886 _92888) = (term620 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6979277 (term469 _128066 x'' _92887 _92888 _92886) (term478 _128066 _92886) (term588 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979312 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979313 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term621 _128066 _92889 _92887 _92886 _92888) = (term622 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979312 (term434 _128066 _92887 _92886 _92888) (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979319 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term444 _128066 _92889 _92886) = (term444 _128066 _92889 _92886).
Proof. exact (eq_refl (term444 _128066 _92889 _92886)). Qed.
Lemma lem6979320 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term588 _128066 _92889 _92887 _92886 _92888) = (term623 _128066 _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979319 _128066 _92889 _92886) (@lem6979313 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979324 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979325 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term623 _128066 _92886 _92887 _92889 _92888) = (term624 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979324 (term434 _128066 _92887 _92886 _92888) (term400 _128066 _92889 _92886) (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979341 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term588 _128066 _92889 _92887 _92886 _92888) = (term624 _128066 _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979320 _128066 _92886 _92887 _92889 _92888) (@lem6979325 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979342 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6979343 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term625 _128066 _92889 _92887 _92886 _92888) = (term626 _128066 _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979342 _128066 _92886) (@lem6979341 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979347 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979348 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term626 _128066 _92886 _92887 _92889 _92888) = (term627 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979347 (term434 _128066 _92887 _92886 _92888) (term478 _128066 _92886) (term445 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979374 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term625 _128066 _92889 _92887 _92886 _92888) = (term627 _128066 _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979343 _128066 _92886 _92887 _92889 _92888) (@lem6979348 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979375 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term589 _128066 x'' _92887 _92888 _92886) = (term589 _128066 x'' _92887 _92888 _92886).
Proof. exact (eq_refl (term589 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979376 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term620 _128066 x'' _92889 _92887 _92886 _92888) = (term628 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979375 _128066 x'' _92887 _92888 _92886) (@lem6979374 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979387 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term591 _128066 x'' _92889 _92887 _92886 _92888) = (term628 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979278 _128066 x'' _92889 _92887 _92886 _92888) (@lem6979376 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6979389 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term629 _128066 x'' _92889 _92887 _92886 _92888) = (term630 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979388) (@lem6979387 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979423 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979424 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term621 _128066 _92889 _92887 _92886 _92888) = (term622 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979423 (term434 _128066 _92887 _92886 _92888) (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979430 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term444 _128066 _92889 _92886) = (term444 _128066 _92889 _92886).
Proof. exact (eq_refl (term444 _128066 _92889 _92886)). Qed.
Lemma lem6979431 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term588 _128066 _92889 _92887 _92886 _92888) = (term623 _128066 _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979430 _128066 _92889 _92886) (@lem6979424 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979435 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979436 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term623 _128066 _92886 _92887 _92889 _92888) = (term624 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979435 (term434 _128066 _92887 _92886 _92888) (term400 _128066 _92889 _92886) (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979452 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term588 _128066 _92889 _92887 _92886 _92888) = (term624 _128066 _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979431 _128066 _92886 _92887 _92889 _92888) (@lem6979436 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979453 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6979454 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term625 _128066 _92889 _92887 _92886 _92888) = (term626 _128066 _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979453 _128066 _92886) (@lem6979452 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979458 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979459 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term626 _128066 _92886 _92887 _92889 _92888) = (term627 _128066 _92886 _92887 _92889 _92888).
Proof. exact (@lem6979458 (term434 _128066 _92887 _92886 _92888) (term478 _128066 _92886) (term445 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979485 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term625 _128066 _92889 _92887 _92886 _92888) = (term627 _128066 _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979454 _128066 _92886 _92887 _92889 _92888) (@lem6979459 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979486 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term589 _128066 x'' _92887 _92888 _92886) = (term589 _128066 x'' _92887 _92888 _92886).
Proof. exact (eq_refl (term589 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979487 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term620 _128066 x'' _92889 _92887 _92886 _92888) = (term628 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979486 _128066 x'' _92887 _92888 _92886) (@lem6979485 _128066 _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979498 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : ((term591 _128066 x'' _92889 _92887 _92886 _92888) = (term620 _128066 x'' _92889 _92887 _92886 _92888)) = ((term628 _128066 x'' _92886 _92887 _92889 _92888) = (term628 _128066 x'' _92886 _92887 _92889 _92888)).
Proof. exact (MK_COMB (@lem6979389 _128066 x'' _92886 _92887 _92889 _92888) (@lem6979487 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979500 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6979501 (x : Prop) : (x = x) = True.
Proof. exact (@lem6979500 Prop x). Qed.
Lemma lem6979502 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : ((term628 _128066 x'' _92886 _92887 _92889 _92888) = (term628 _128066 x'' _92886 _92887 _92889 _92888)) = True.
Proof. exact (@lem6979501 (term628 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979503 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : ((term591 _128066 x'' _92889 _92887 _92886 _92888) = (term620 _128066 x'' _92889 _92887 _92886 _92888)) = True.
Proof. exact (TRANS (@lem6979498 _128066 x'' _92886 _92887 _92889 _92888) (@lem6979502 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6979504 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : True = ((term591 _128066 x'' _92889 _92887 _92886 _92888) = (term620 _128066 x'' _92889 _92887 _92886 _92888)).
Proof. exact (SYM (@lem6979503 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979505 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term591 _128066 x'' _92889 _92887 _92886 _92888) = (term620 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (EQ_MP (@lem6979504 _128066 x'' _92889 _92887 _92886 _92888) (@lem0)). Qed.
Lemma lem6979506 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term620 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6979505 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978666 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6979508 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6979509 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term620 _128066 x'' _92889 _92887 _92886 _92888) = (term631 _128066 _92889 x'' _92887 _92888 _92886).
Proof. exact (@lem6979508 (term625 _128066 _92889 _92887 _92886 _92888) (term469 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979511 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6979512 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term634 _128066 _92889 _92887 _92886 _92888) = (term635 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6979511 (term478 _128066 _92886) (term588 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979514 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979515 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term636 _128066 _92886) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) _92886).
Proof. exact (@lem6979514 (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) _92886)). Qed.
Lemma lem6979516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6979517 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term637 _128066 _92886) = (term500 _128066 _92886).
Proof. exact (MK_COMB (@lem6979516) (@lem6979515 _128066 _92886)). Qed.
Lemma lem6979519 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6979520 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term638 _128066 _92889 _92887 _92886 _92888) = (term639 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6979519 (term400 _128066 _92889 _92886) (term621 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979522 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979523 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term611 _128066 _92889 _92886) = (term399 _128066 _92889 _92886).
Proof. exact (@lem6979522 (term399 _128066 _92889 _92886)). Qed.
Lemma lem6979524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6979525 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term640 _128066 _92889 _92886) = (term641 _128066 _92889 _92886).
Proof. exact (MK_COMB (@lem6979524) (@lem6979523 _128066 _92889 _92886)). Qed.
Lemma lem6979527 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6979528 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term642 _128066 _92889 _92887 _92886 _92888) = (term643 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6979527 (term442 _128066 _92887 _92889 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979530 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979531 {_128066 : Type'} (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term644 _128066 _92887 _92889 _92888) = (term440 _128066 _92887 _92889 _92888).
Proof. exact (@lem6979530 (term440 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6979533 {_128066 : Type'} (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term645 _128066 _92887 _92889 _92888) = (term646 _128066 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6979532) (@lem6979531 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979534 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term495 _128066 _92887 _92886 _92888) = (term495 _128066 _92887 _92886 _92888).
Proof. exact (eq_refl (term495 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979535 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term643 _128066 _92889 _92887 _92886 _92888) = (term647 _128066 _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6979533 _128066 _92887 _92889 _92888) (@lem6979534 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979536 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term642 _128066 _92889 _92887 _92886 _92888) = (term647 _128066 _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6979528 _128066 _92889 _92887 _92886 _92888) (@lem6979535 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979537 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term639 _128066 _92889 _92887 _92886 _92888) = (term648 _128066 _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6979525 _128066 _92889 _92886) (@lem6979536 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979538 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term638 _128066 _92889 _92887 _92886 _92888) = (term648 _128066 _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6979520 _128066 _92889 _92887 _92886 _92888) (@lem6979537 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979539 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term635 _128066 _92889 _92887 _92886 _92888) = (term649 _128066 _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6979517 _128066 _92886) (@lem6979538 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979540 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term634 _128066 _92889 _92887 _92886 _92888) = (term649 _128066 _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6979512 _128066 _92889 _92887 _92886 _92888) (@lem6979539 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6979542 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term650 _128066 _92889 _92887 _92886 _92888) = (term651 _128066 _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6979541) (@lem6979540 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979543 {_128066 : Type'} (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term469 _128066 x'' _92887 _92888 _92886) = (term469 _128066 x'' _92887 _92888 _92886).
Proof. exact (eq_refl (term469 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979544 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term631 _128066 _92889 x'' _92887 _92888 _92886) = (term652 _128066 _92889 x'' _92887 _92888 _92886).
Proof. exact (MK_COMB (@lem6979542 _128066 _92889 _92887 _92886 _92888) (@lem6979543 _128066 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979545 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) : (term620 _128066 x'' _92889 _92887 _92886 _92888) = (term652 _128066 _92889 x'' _92887 _92888 _92886).
Proof. exact (TRANS (@lem6979509 _128066 _92889 x'' _92887 _92888 _92886) (@lem6979544 _128066 _92889 x'' _92887 _92888 _92886)). Qed.
Lemma lem6979547 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term653 _128066 x f s b.
Proof. exact (conj (@lem6979264 _128066 x f s b h1 h2 h3) (@lem6979271 _128066 f s b h3)). Qed.
Lemma lem6979548 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term654 _128066 x f s b.
Proof. exact (conj (@lem6979191 _128066 s x h1 h2) (@lem6979547 _128066 x f s b h1 h2 h3)). Qed.
Lemma lem6979549 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term655 _128066 x f s b.
Proof. exact (conj (@lem6979165 _128066 f s b h3) (@lem6979548 _128066 x f s b h1 h2 h3)). Qed.
Lemma lem6979551 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term652 _128066 _92889 x'' _92887 _92888 _92886.
Proof. exact (EQ_MP (@lem6979545 _128066 _92889 x'' _92887 _92888 _92886) (@lem6979506 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6979552 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92888 : nat) (_92886 : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term652 _128066 _92889 x'' _92887 _92888 _92886.
Proof. exact (@lem6979551 _128066 _92889 _92887 _92888 _92886 x'' h1). Qed.
Lemma lem6979553 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term656 _128066 x x'' f b s.
Proof. exact (@lem6979552 _128066 (@I ((_128066 -> Prop) -> _128066) x s) f b s x'' h1). Qed.
Lemma lem6979556 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term469 _128066 x'' f b s.
Proof. exact (@lem6979553 _128066 x f b s x'' h1 (@lem6979549 _128066 x f s b h2 h3 h4)). Qed.
Lemma lem6979557 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term657 _128066 x'' f b s.
Proof. exact (fun h0 : term658 _128066 x'' f b s => @lem6979556 _128066 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem6979559 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979560 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (b : nat) (s : _128066 -> Prop) : (term657 _128066 x'' f b s) = (term469 _128066 x'' f b s).
Proof. exact (@lem6979559 (term469 _128066 x'' f b s)). Qed.
Lemma lem6979561 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term469 _128066 x'' f b s.
Proof. exact (EQ_MP (@lem6979560 _128066 x'' f b s) (@lem6979557 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6979563 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term614 _128066 s f _92890 b.
Proof. exact (EQ_MP (@lem6979251 _128066 s f _92890 b) (@lem6979240 _128066 _92890 f s b h1)). Qed.
Lemma lem6979564 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term614 _128066 s f _92890 b.
Proof. exact (@lem6979563 _128066 _92890 f s b h1). Qed.
Lemma lem6979565 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term659 _128066 x'' s f b.
Proof. exact (@lem6979564 _128066 (term450 _128066 x'' s f b) f s b h1). Qed.
Lemma lem6979568 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term660 _128066 x'' s f b.
Proof. exact (@lem6979565 _128066 x'' f s b h4 (@lem6979561 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6979569 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term661 _128066 x'' s f b.
Proof. exact (fun h0 : term662 _128066 x'' s f b => @lem6979568 _128066 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem6979571 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979572 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term661 _128066 x'' s f b) = (term660 _128066 x'' s f b).
Proof. exact (@lem6979571 (term660 _128066 x'' s f b)). Qed.
Lemma lem6979573 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term29 _128066 s) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term660 _128066 x'' s f b.
Proof. exact (EQ_MP (@lem6979572 _128066 x'' s f b) (@lem6979569 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6979579 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979580 (_92880 : nat) (_92881 : nat) : (term394 _92880 _92881) = (term663 _92880 _92881).
Proof. exact (@lem6979579 (term388 _92880 _92881) (term391 _92880 _92881)). Qed.
Lemma lem6979586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6979587 (_92880 : nat) (_92881 : nat) : (term664 _92880 _92881) = (term665 _92880 _92881).
Proof. exact (MK_COMB (@lem6979586) (@lem6979580 _92880 _92881)). Qed.
Lemma lem6979593 (_92880 : nat) (_92881 : nat) : (term663 _92880 _92881) = (term663 _92880 _92881).
Proof. exact (eq_refl (term663 _92880 _92881)). Qed.
Lemma lem6979594 (_92880 : nat) (_92881 : nat) : ((term394 _92880 _92881) = (term663 _92880 _92881)) = ((term663 _92880 _92881) = (term663 _92880 _92881)).
Proof. exact (MK_COMB (@lem6979587 _92880 _92881) (@lem6979593 _92880 _92881)). Qed.
Lemma lem6979596 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6979597 (x : Prop) : (x = x) = True.
Proof. exact (@lem6979596 Prop x). Qed.
Lemma lem6979598 (_92880 : nat) (_92881 : nat) : ((term663 _92880 _92881) = (term663 _92880 _92881)) = True.
Proof. exact (@lem6979597 (term663 _92880 _92881)). Qed.
Lemma lem6979599 (_92880 : nat) (_92881 : nat) : ((term394 _92880 _92881) = (term663 _92880 _92881)) = True.
Proof. exact (TRANS (@lem6979594 _92880 _92881) (@lem6979598 _92880 _92881)). Qed.
Lemma lem6979600 (_92880 : nat) (_92881 : nat) : True = ((term394 _92880 _92881) = (term663 _92880 _92881)).
Proof. exact (SYM (@lem6979599 _92880 _92881)). Qed.
Lemma lem6979601 (_92880 : nat) (_92881 : nat) : (term394 _92880 _92881) = (term663 _92880 _92881).
Proof. exact (EQ_MP (@lem6979600 _92880 _92881) (@lem0)). Qed.
Lemma lem6979602 (_92880 : nat) (_92881 : nat) (h1 : term38) : term663 _92880 _92881.
Proof. exact (EQ_MP (@lem6979601 _92880 _92881) (@lem6978618 _92880 _92881 h1)). Qed.
Lemma lem6979604 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6979605 (_92880 : nat) (_92881 : nat) : (term663 _92880 _92881) = (term666 _92880 _92881).
Proof. exact (@lem6979604 (term391 _92880 _92881) (term388 _92880 _92881)). Qed.
Lemma lem6979607 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979608 (_92880 : nat) (_92881 : nat) : (term667 _92880 _92881) = (term389 _92880 _92881).
Proof. exact (@lem6979607 (term389 _92880 _92881)). Qed.
Lemma lem6979609 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6979610 (_92880 : nat) (_92881 : nat) : (term668 _92880 _92881) = (term669 _92880 _92881).
Proof. exact (MK_COMB (@lem6979609) (@lem6979608 _92880 _92881)). Qed.
Lemma lem6979611 (_92880 : nat) (_92881 : nat) : (term388 _92880 _92881) = (term388 _92880 _92881).
Proof. exact (eq_refl (term388 _92880 _92881)). Qed.
Lemma lem6979612 (_92880 : nat) (_92881 : nat) : (term666 _92880 _92881) = (term670 _92880 _92881).
Proof. exact (MK_COMB (@lem6979610 _92880 _92881) (@lem6979611 _92880 _92881)). Qed.
Lemma lem6979613 (_92880 : nat) (_92881 : nat) : (term663 _92880 _92881) = (term670 _92880 _92881).
Proof. exact (TRANS (@lem6979605 _92880 _92881) (@lem6979612 _92880 _92881)). Qed.
Lemma lem6979616 (_92880 : nat) (_92881 : nat) (h1 : term38) : term670 _92880 _92881.
Proof. exact (EQ_MP (@lem6979613 _92880 _92881) (@lem6979602 _92880 _92881 h1)). Qed.
Lemma lem6979617 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) (h1 : term38) : term671 _128066 x'' s f b.
Proof. exact (@lem6979616 (term453 _128066 x'' s f b) b h1). Qed.
Lemma lem6979620 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term460 _128066 x'' s f b.
Proof. exact (@lem6979617 _128066 x'' s f b h2 (@lem6979573 _128066 x'' x f s b h1 h3 h4 h5)). Qed.
Lemma lem6979621 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term672 _128066 x'' s f b.
Proof. exact (fun h0 : term462 _128066 x'' s f b => @lem6979620 _128066 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem6979623 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979624 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (f : _128066 -> nat) (b : nat) : (term672 _128066 x'' s f b) = (term460 _128066 x'' s f b).
Proof. exact (@lem6979623 (term460 _128066 x'' s f b)). Qed.
Lemma lem6979625 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term460 _128066 x'' s f b.
Proof. exact (EQ_MP (@lem6979624 _128066 x'' s f b) (@lem6979621 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6979628 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (h1). Qed.
Lemma lem6979629 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term600 _128066 s.
Proof. exact (fun h0 : s = (@EMPTY _128066) => @lem6979628 _128066 s h1). Qed.
Lemma lem6979631 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6979632 {_128066 : Type'} (s : _128066 -> Prop) : (term600 _128066 s) = (term29 _128066 s).
Proof. exact (@lem6979631 (s = (@EMPTY _128066))). Qed.
Lemma lem6979633 {_128066 : Type'} (s : _128066 -> Prop) (h1 : term29 _128066 s) : term29 _128066 s.
Proof. exact (EQ_MP (@lem6979632 _128066 s) (@lem6979629 _128066 s h1)). Qed.
Lemma lem6979635 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (EQ_MP (@lem6979178 _128066 x _92891) (@lem6978636 _128066 _92891 x h1)). Qed.
Lemma lem6979636 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x _92891.
Proof. exact (@lem6979635 _128066 _92891 x h1). Qed.
Lemma lem6979637 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term603 _128066 x s.
Proof. exact (@lem6979636 _128066 s x h1). Qed.
Lemma lem6979640 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (@lem6979637 _128066 s x h2 (@lem6979633 _128066 s h1)). Qed.
Lemma lem6979641 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term604 _128066 x s.
Proof. exact (fun h0 : term605 _128066 x s => @lem6979640 _128066 s x h1 h2). Qed.
Lemma lem6979643 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6979644 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term604 _128066 x s) = (term413 _128066 x s).
Proof. exact (@lem6979643 (term413 _128066 x s)). Qed.
Lemma lem6979645 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term29 _128066 s) (h2 : term384 _128066 x) : term413 _128066 x s.
Proof. exact (EQ_MP (@lem6979644 _128066 x s) (@lem6979641 _128066 s x h1 h2)). Qed.
Lemma lem6979647 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term495 _128066 f s b.
Proof. exact (proj2 (@lem6978178 _128066 f s b h1)). Qed.
Lemma lem6979648 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term619 _128066 f s b.
Proof. exact (fun h0 : term434 _128066 f s b => @lem6979647 _128066 f s b h1). Qed.
Lemma lem6979650 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6979651 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) : (term619 _128066 f s b) = (term495 _128066 f s b).
Proof. exact (@lem6979650 (term434 _128066 f s b)). Qed.
Lemma lem6979652 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term495 _128066 f s b.
Proof. exact (EQ_MP (@lem6979651 _128066 f s b) (@lem6979648 _128066 f s b h1)). Qed.
Lemma lem6979668 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979669 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term596 _128066 x'' _92889 _92887 _92886 _92888) = (term673 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6979668 (term400 _128066 _92889 _92886) (term462 _128066 x'' _92886 _92887 _92888) (term621 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979683 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979684 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term674 _128066 x'' _92889 _92887 _92886 _92888) = (term675 _128066 _92889 x'' _92887 _92886 _92888).
Proof. exact (@lem6979683 (term442 _128066 _92887 _92889 _92888) (term462 _128066 x'' _92886 _92887 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979698 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979699 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term676 _128066 x'' _92887 _92886 _92888) = (term677 _128066 x'' _92886 _92887 _92888).
Proof. exact (@lem6979698 (term434 _128066 _92887 _92886 _92888) (term462 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979705 {_128066 : Type'} (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term678 _128066 _92887 _92889 _92888) = (term678 _128066 _92887 _92889 _92888).
Proof. exact (eq_refl (term678 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979706 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term675 _128066 _92889 x'' _92887 _92886 _92888) = (term679 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979705 _128066 _92887 _92889 _92888) (@lem6979699 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979710 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979711 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term679 _128066 _92889 x'' _92886 _92887 _92888) = (term680 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979710 (term434 _128066 _92887 _92886 _92888) (term442 _128066 _92887 _92889 _92888) (term462 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979727 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term675 _128066 _92889 x'' _92887 _92886 _92888) = (term680 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979706 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979711 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979728 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term674 _128066 x'' _92889 _92887 _92886 _92888) = (term680 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979684 _128066 _92889 x'' _92887 _92886 _92888) (@lem6979727 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979729 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term444 _128066 _92889 _92886) = (term444 _128066 _92889 _92886).
Proof. exact (eq_refl (term444 _128066 _92889 _92886)). Qed.
Lemma lem6979730 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term673 _128066 x'' _92889 _92887 _92886 _92888) = (term681 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979729 _128066 _92889 _92886) (@lem6979728 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979734 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979735 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term681 _128066 _92889 x'' _92886 _92887 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979734 (term434 _128066 _92887 _92886 _92888) (term400 _128066 _92889 _92886) (term683 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979761 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term673 _128066 x'' _92889 _92887 _92886 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979730 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979735 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979762 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term596 _128066 x'' _92889 _92887 _92886 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979669 _128066 x'' _92889 _92887 _92886 _92888) (@lem6979761 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979763 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6979764 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term597 _128066 x'' _92889 _92887 _92886 _92888) = (term684 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979763 _128066 _92886) (@lem6979762 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979768 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979769 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term684 _128066 _92889 x'' _92886 _92887 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979768 (term434 _128066 _92887 _92886 _92888) (term478 _128066 _92886) (term686 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979805 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term597 _128066 x'' _92889 _92887 _92886 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979764 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979769 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6979807 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term687 _128066 x'' _92889 _92887 _92886 _92888) = (term688 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979806) (@lem6979805 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979811 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979812 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term689 _128066 x'' _92889 _92887 _92886 _92888) = (term690 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6979811 (term478 _128066 _92886) (term442 _128066 _92887 _92889 _92888) (term691 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979836 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979837 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term691 _128066 x'' _92889 _92887 _92886 _92888) = (term692 _128066 _92889 x'' _92887 _92886 _92888).
Proof. exact (@lem6979836 (term400 _128066 _92889 _92886) (term462 _128066 x'' _92886 _92887 _92888) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979851 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6979852 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term676 _128066 x'' _92887 _92886 _92888) = (term677 _128066 x'' _92886 _92887 _92888).
Proof. exact (@lem6979851 (term434 _128066 _92887 _92886 _92888) (term462 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979858 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term444 _128066 _92889 _92886) = (term444 _128066 _92889 _92886).
Proof. exact (eq_refl (term444 _128066 _92889 _92886)). Qed.
Lemma lem6979859 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term692 _128066 _92889 x'' _92887 _92886 _92888) = (term693 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979858 _128066 _92889 _92886) (@lem6979852 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979863 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979864 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term693 _128066 _92889 x'' _92886 _92887 _92888) = (term694 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979863 (term434 _128066 _92887 _92886 _92888) (term400 _128066 _92889 _92886) (term462 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979880 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term692 _128066 _92889 x'' _92887 _92886 _92888) = (term694 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979859 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979864 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979881 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term691 _128066 x'' _92889 _92887 _92886 _92888) = (term694 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979837 _128066 _92889 x'' _92887 _92886 _92888) (@lem6979880 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979882 {_128066 : Type'} (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term678 _128066 _92887 _92889 _92888) = (term678 _128066 _92887 _92889 _92888).
Proof. exact (eq_refl (term678 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979883 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term695 _128066 x'' _92889 _92887 _92886 _92888) = (term696 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979882 _128066 _92887 _92889 _92888) (@lem6979881 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979888 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term696 _128066 _92889 x'' _92886 _92887 _92888) = (term697 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979887 (term434 _128066 _92887 _92886 _92888) (term442 _128066 _92887 _92889 _92888) (term698 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979902 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979903 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term699 _128066 _92889 x'' _92886 _92887 _92888) = (term686 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979902 (term400 _128066 _92889 _92886) (term442 _128066 _92887 _92889 _92888) (term462 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979919 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term700 _128066 _92887 _92886 _92888) = (term700 _128066 _92887 _92886 _92888).
Proof. exact (eq_refl (term700 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6979920 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term697 _128066 _92889 x'' _92886 _92887 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979919 _128066 _92887 _92886 _92888) (@lem6979903 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979931 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term696 _128066 _92889 x'' _92886 _92887 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979888 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979920 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979932 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term695 _128066 x'' _92889 _92887 _92886 _92888) = (term682 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979883 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979931 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979933 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term479 _128066 _92886) = (term479 _128066 _92886).
Proof. exact (eq_refl (term479 _128066 _92886)). Qed.
Lemma lem6979934 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term690 _128066 x'' _92889 _92887 _92886 _92888) = (term684 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6979933 _128066 _92886) (@lem6979932 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979938 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6979939 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term684 _128066 _92889 x'' _92886 _92887 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (@lem6979938 (term434 _128066 _92887 _92886 _92888) (term478 _128066 _92886) (term686 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979975 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term690 _128066 x'' _92889 _92887 _92886 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979934 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979939 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979976 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term689 _128066 x'' _92889 _92887 _92886 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888).
Proof. exact (TRANS (@lem6979812 _128066 x'' _92889 _92887 _92886 _92888) (@lem6979975 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979977 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : ((term597 _128066 x'' _92889 _92887 _92886 _92888) = (term689 _128066 x'' _92889 _92887 _92886 _92888)) = ((term685 _128066 _92889 x'' _92886 _92887 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888)).
Proof. exact (MK_COMB (@lem6979807 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979976 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979979 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6979980 (x : Prop) : (x = x) = True.
Proof. exact (@lem6979979 Prop x). Qed.
Lemma lem6979981 {_128066 : Type'} (_92889 : _128066) (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : ((term685 _128066 _92889 x'' _92886 _92887 _92888) = (term685 _128066 _92889 x'' _92886 _92887 _92888)) = True.
Proof. exact (@lem6979980 (term685 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979982 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : ((term597 _128066 x'' _92889 _92887 _92886 _92888) = (term689 _128066 x'' _92889 _92887 _92886 _92888)) = True.
Proof. exact (TRANS (@lem6979977 _128066 _92889 x'' _92886 _92887 _92888) (@lem6979981 _128066 _92889 x'' _92886 _92887 _92888)). Qed.
Lemma lem6979983 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : True = ((term597 _128066 x'' _92889 _92887 _92886 _92888) = (term689 _128066 x'' _92889 _92887 _92886 _92888)).
Proof. exact (SYM (@lem6979982 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979984 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term597 _128066 x'' _92889 _92887 _92886 _92888) = (term689 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (EQ_MP (@lem6979983 _128066 x'' _92889 _92887 _92886 _92888) (@lem0)). Qed.
Lemma lem6979985 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term689 _128066 x'' _92889 _92887 _92886 _92888.
Proof. exact (EQ_MP (@lem6979984 _128066 x'' _92889 _92887 _92886 _92888) (@lem6978690 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6979987 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6979988 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term689 _128066 x'' _92889 _92887 _92886 _92888) = (term701 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (@lem6979987 (term702 _128066 x'' _92889 _92887 _92886 _92888) (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6979990 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6979991 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term703 _128066 x'' _92889 _92887 _92886 _92888) = (term704 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6979990 (term478 _128066 _92886) (term691 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6979993 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6979994 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term636 _128066 _92886) = (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) _92886).
Proof. exact (@lem6979993 (@I ((_128066 -> Prop) -> Prop) (@FINITE _128066) _92886)). Qed.
Lemma lem6979995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6979996 {_128066 : Type'} (_92886 : _128066 -> Prop) : (term637 _128066 _92886) = (term500 _128066 _92886).
Proof. exact (MK_COMB (@lem6979995) (@lem6979994 _128066 _92886)). Qed.
Lemma lem6979998 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6979999 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term705 _128066 x'' _92889 _92887 _92886 _92888) = (term706 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (@lem6979998 (term462 _128066 x'' _92886 _92887 _92888) (term707 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980001 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6980002 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term708 _128066 x'' _92886 _92887 _92888) = (term460 _128066 x'' _92886 _92887 _92888).
Proof. exact (@lem6980001 (term460 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6980003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980004 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92888 : nat) : (term709 _128066 x'' _92886 _92887 _92888) = (term710 _128066 x'' _92886 _92887 _92888).
Proof. exact (MK_COMB (@lem6980003) (@lem6980002 _128066 x'' _92886 _92887 _92888)). Qed.
Lemma lem6980006 (a : Prop) (b : Prop) : (term632 a b) = (term633 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6980007 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term711 _128066 _92889 _92887 _92886 _92888) = (term712 _128066 _92889 _92887 _92886 _92888).
Proof. exact (@lem6980006 (term400 _128066 _92889 _92886) (term434 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6980009 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6980010 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term611 _128066 _92889 _92886) = (term399 _128066 _92889 _92886).
Proof. exact (@lem6980009 (term399 _128066 _92889 _92886)). Qed.
Lemma lem6980011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6980012 {_128066 : Type'} (_92889 : _128066) (_92886 : _128066 -> Prop) : (term640 _128066 _92889 _92886) = (term641 _128066 _92889 _92886).
Proof. exact (MK_COMB (@lem6980011) (@lem6980010 _128066 _92889 _92886)). Qed.
Lemma lem6980013 {_128066 : Type'} (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term495 _128066 _92887 _92886 _92888) = (term495 _128066 _92887 _92886 _92888).
Proof. exact (eq_refl (term495 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6980014 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term712 _128066 _92889 _92887 _92886 _92888) = (term713 _128066 _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6980012 _128066 _92889 _92886) (@lem6980013 _128066 _92887 _92886 _92888)). Qed.
Lemma lem6980015 {_128066 : Type'} (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term711 _128066 _92889 _92887 _92886 _92888) = (term713 _128066 _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6980007 _128066 _92889 _92887 _92886 _92888) (@lem6980014 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980016 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term706 _128066 x'' _92889 _92887 _92886 _92888) = (term714 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6980004 _128066 x'' _92886 _92887 _92888) (@lem6980015 _128066 _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980017 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term705 _128066 x'' _92889 _92887 _92886 _92888) = (term714 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6979999 _128066 x'' _92889 _92887 _92886 _92888) (@lem6980016 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980018 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term704 _128066 x'' _92889 _92887 _92886 _92888) = (term715 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6979996 _128066 _92886) (@lem6980017 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980019 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term703 _128066 x'' _92889 _92887 _92886 _92888) = (term715 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (TRANS (@lem6979991 _128066 x'' _92889 _92887 _92886 _92888) (@lem6980018 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980020 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6980021 {_128066 : Type'} (x'' : type642 _128066) (_92889 : _128066) (_92887 : _128066 -> nat) (_92886 : _128066 -> Prop) (_92888 : nat) : (term716 _128066 x'' _92889 _92887 _92886 _92888) = (term717 _128066 x'' _92889 _92887 _92886 _92888).
Proof. exact (MK_COMB (@lem6980020) (@lem6980019 _128066 x'' _92889 _92887 _92886 _92888)). Qed.
Lemma lem6980022 {_128066 : Type'} (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term442 _128066 _92887 _92889 _92888) = (term442 _128066 _92887 _92889 _92888).
Proof. exact (eq_refl (term442 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6980023 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term701 _128066 x'' _92886 _92887 _92889 _92888) = (term718 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (MK_COMB (@lem6980021 _128066 x'' _92889 _92887 _92886 _92888) (@lem6980022 _128066 _92887 _92889 _92888)). Qed.
Lemma lem6980024 {_128066 : Type'} (x'' : type642 _128066) (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) : (term689 _128066 x'' _92889 _92887 _92886 _92888) = (term718 _128066 x'' _92886 _92887 _92889 _92888).
Proof. exact (TRANS (@lem6979988 _128066 x'' _92886 _92887 _92889 _92888) (@lem6980023 _128066 x'' _92886 _92887 _92889 _92888)). Qed.
Lemma lem6980026 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term29 _128066 s) (h2 : term384 _128066 x) (h3 : term80 _128066 f s b) : term719 _128066 x f s b.
Proof. exact (conj (@lem6979645 _128066 s x h1 h2) (@lem6979652 _128066 f s b h3)). Qed.
Lemma lem6980027 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term720 _128066 x'' x f s b.
Proof. exact (conj (@lem6979625 _128066 x'' x f s b h1 h2 h3 h4 h5) (@lem6980026 _128066 x f s b h3 h4 h5)). Qed.
Lemma lem6980028 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term721 _128066 x'' x f s b.
Proof. exact (conj (@lem6979158 _128066 f s b h5) (@lem6980027 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980030 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term718 _128066 x'' _92886 _92887 _92889 _92888.
Proof. exact (EQ_MP (@lem6980024 _128066 x'' _92886 _92887 _92889 _92888) (@lem6979985 _128066 _92889 _92887 _92886 _92888 x'' h1)). Qed.
Lemma lem6980031 {_128066 : Type'} (_92886 : _128066 -> Prop) (_92887 : _128066 -> nat) (_92889 : _128066) (_92888 : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term718 _128066 x'' _92886 _92887 _92889 _92888.
Proof. exact (@lem6980030 _128066 _92886 _92887 _92889 _92888 x'' h1). Qed.
Lemma lem6980032 {_128066 : Type'} (f : _128066 -> nat) (x : type684 _128066) (s : _128066 -> Prop) (b : nat) (x'' : type642 _128066) (h1 : term273 _128066 x'') : term722 _128066 x'' f x s b.
Proof. exact (@lem6980031 _128066 s f (@I ((_128066 -> Prop) -> _128066) x s) b x'' h1). Qed.
Lemma lem6980035 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term618 _128066 f x s b.
Proof. exact (@lem6980032 _128066 f x s b x'' h1 (@lem6980028 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980036 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term723 _128066 f x s b.
Proof. exact (fun h0 : term616 _128066 f x s b => @lem6980035 _128066 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem6980038 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6980039 {_128066 : Type'} (f : _128066 -> nat) (x : type684 _128066) (s : _128066 -> Prop) (b : nat) : (term723 _128066 f x s b) = (term618 _128066 f x s b).
Proof. exact (@lem6980038 (term616 _128066 f x s b)). Qed.
Lemma lem6980040 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term618 _128066 f x s b.
Proof. exact (EQ_MP (@lem6980039 _128066 f x s b) (@lem6980036 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980042 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6980045 {_128066 : Type'} (f : _128066 -> nat) (b : nat) (_92890 : _128066) (s : _128066 -> Prop) : (term496 _128066 s f _92890 b) = (term724 _128066 f b _92890 s).
Proof. exact (@lem6980042 (term440 _128066 f _92890 b) (term400 _128066 _92890 s)). Qed.
Lemma lem6980048 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term724 _128066 f b _92890 s.
Proof. exact (EQ_MP (@lem6980045 _128066 f b _92890 s) (@lem6978630 _128066 _92890 f s b h1)). Qed.
Lemma lem6980049 {_128066 : Type'} (_92890 : _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term724 _128066 f b _92890 s.
Proof. exact (@lem6980048 _128066 _92890 f s b h1). Qed.
Lemma lem6980050 {_128066 : Type'} (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term725 _128066 f b x s.
Proof. exact (@lem6980049 _128066 (@I ((_128066 -> Prop) -> _128066) x s) f s b h1). Qed.
Lemma lem6980053 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term605 _128066 x s.
Proof. exact (@lem6980050 _128066 x f s b h5 (@lem6980040 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980054 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term726 _128066 x s.
Proof. exact (fun h0 : term413 _128066 x s => @lem6980053 _128066 x'' x f s b h1 h2 h3 h4 h5). Qed.
Lemma lem6980056 (p : Prop) : (term601 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem6980057 {_128066 : Type'} (x : type684 _128066) (s : _128066 -> Prop) : (term726 _128066 x s) = (term605 _128066 x s).
Proof. exact (@lem6980056 (term413 _128066 x s)). Qed.
Lemma lem6980058 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : term605 _128066 x s.
Proof. exact (EQ_MP (@lem6980057 _128066 x s) (@lem6980054 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980064 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6980065 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term416 _128066 x _92891) = (term727 _128066 x _92891).
Proof. exact (@lem6980064 (_92891 = (@EMPTY _128066)) (term413 _128066 x _92891)). Qed.
Lemma lem6980073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6980074 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term728 _128066 x _92891) = (term729 _128066 x _92891).
Proof. exact (MK_COMB (@lem6980073) (@lem6980065 _128066 x _92891)). Qed.
Lemma lem6980082 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term727 _128066 x _92891) = (term727 _128066 x _92891).
Proof. exact (eq_refl (term727 _128066 x _92891)). Qed.
Lemma lem6980083 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : ((term416 _128066 x _92891) = (term727 _128066 x _92891)) = ((term727 _128066 x _92891) = (term727 _128066 x _92891)).
Proof. exact (MK_COMB (@lem6980074 _128066 x _92891) (@lem6980082 _128066 x _92891)). Qed.
Lemma lem6980085 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6980086 (x : Prop) : (x = x) = True.
Proof. exact (@lem6980085 Prop x). Qed.
Lemma lem6980087 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : ((term727 _128066 x _92891) = (term727 _128066 x _92891)) = True.
Proof. exact (@lem6980086 (term727 _128066 x _92891)). Qed.
Lemma lem6980088 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : ((term416 _128066 x _92891) = (term727 _128066 x _92891)) = True.
Proof. exact (TRANS (@lem6980083 _128066 x _92891) (@lem6980087 _128066 x _92891)). Qed.
Lemma lem6980089 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : True = ((term416 _128066 x _92891) = (term727 _128066 x _92891)).
Proof. exact (SYM (@lem6980088 _128066 x _92891)). Qed.
Lemma lem6980090 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term416 _128066 x _92891) = (term727 _128066 x _92891).
Proof. exact (EQ_MP (@lem6980089 _128066 x _92891) (@lem0)). Qed.
Lemma lem6980091 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term727 _128066 x _92891.
Proof. exact (EQ_MP (@lem6980090 _128066 x _92891) (@lem6978636 _128066 _92891 x h1)). Qed.
Lemma lem6980093 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6980096 {_128066 : Type'} (x : type684 _128066) (_92891 : _128066 -> Prop) : (term727 _128066 x _92891) = (term730 _128066 x _92891).
Proof. exact (@lem6980093 (term413 _128066 x _92891) (_92891 = (@EMPTY _128066))). Qed.
Lemma lem6980099 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term730 _128066 x _92891.
Proof. exact (EQ_MP (@lem6980096 _128066 x _92891) (@lem6980091 _128066 _92891 x h1)). Qed.
Lemma lem6980100 {_128066 : Type'} (_92891 : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term730 _128066 x _92891.
Proof. exact (@lem6980099 _128066 _92891 x h1). Qed.
Lemma lem6980101 {_128066 : Type'} (s : _128066 -> Prop) (x : type684 _128066) (h1 : term384 _128066 x) : term730 _128066 x s.
Proof. exact (@lem6980100 _128066 s x h1). Qed.
Lemma lem6980104 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term29 _128066 s) (h4 : term384 _128066 x) (h5 : term80 _128066 f s b) : s = (@EMPTY _128066).
Proof. exact (@lem6980101 _128066 s x h4 (@lem6980058 _128066 x'' x f s b h1 h2 h3 h4 h5)). Qed.
Lemma lem6980105 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term731 _128066 s.
Proof. exact (fun h0 : term29 _128066 s => @lem6980104 _128066 x'' x f s b h1 h2 h0 h3 h4). Qed.
Lemma lem6980107 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6980108 {_128066 : Type'} (s : _128066 -> Prop) : (term731 _128066 s) = (s = (@EMPTY _128066)).
Proof. exact (@lem6980107 (s = (@EMPTY _128066))). Qed.
Lemma lem6980109 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : s = (@EMPTY _128066).
Proof. exact (EQ_MP (@lem6980108 _128066 s) (@lem6980105 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6980112 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6980114 {_128066 : Type'} (s : _128066 -> Prop) : (term29 _128066 s) = (term732 _128066 s).
Proof. exact (@lem6980112 (s = (@EMPTY _128066))). Qed.
Lemma lem6980117 {_128066 : Type'} (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term80 _128066 f s b) : term732 _128066 s.
Proof. exact (EQ_MP (@lem6980114 _128066 s) (@lem6978624 _128066 f s b h1)). Qed.
Lemma lem6980120 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : False.
Proof. exact (@lem6980117 _128066 f s b h4 (@lem6980109 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6980121 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : term733.
Proof. exact (fun h0 : ~ False => @lem6980120 _128066 x'' x f s b h1 h2 h3 h4). Qed.
Lemma lem6980123 (p : Prop) : (term599 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6980124 : term733 = False.
Proof. exact (@lem6980123 False). Qed.
Lemma lem6980125 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (b : nat) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term384 _128066 x) (h4 : term80 _128066 f s b) : False.
Proof. exact (EQ_MP (@lem6980124) (@lem6980121 _128066 x'' x f s b h1 h2 h3 h4)). Qed.
Lemma lem6980126 {_128066 : Type'} (x'' : type642 _128066) (f : _128066 -> nat) (s : _128066 -> Prop) (x : type684 _128066) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term90 _128066 f s) (h4 : term384 _128066 x) : False.
Proof. exact (ex_elim (@lem6977464 _128066 f s h3) (fun b : nat => fun h0 : term89 _128066 f s b => @lem6980125 _128066 x'' x f s b h1 h2 h4 h0)). Qed.
Lemma lem6980127 {_128066 : Type'} (x'' : type642 _128066) (s : _128066 -> Prop) (x : type684 _128066) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term99 _128066 s) (h4 : term384 _128066 x) : False.
Proof. exact (ex_elim (@lem6977463 _128066 s h3) (fun f : _128066 -> nat => fun h0 : term98 _128066 s f => @lem6980126 _128066 x'' f s x h1 h2 h0 h4)). Qed.
Lemma lem6980128 {_128066 : Type'} (x'' : type642 _128066) (x : type684 _128066) (h1 : term273 _128066 x'') (h2 : term38) (h3 : term10 _128066) (h4 : term384 _128066 x) : False.
Proof. exact (ex_elim (@lem6976347 _128066 h3) (fun s : _128066 -> Prop => fun h0 : term106 _128066 s => @lem6980127 _128066 x'' s x h1 h2 h0 h4)). Qed.
Lemma lem6980129 {_128066 : Type'} (x : type684 _128066) (h1 : term12 _128066) (h2 : term38) (h3 : term10 _128066) (h4 : term384 _128066 x) : False.
Proof. exact (ex_elim (@lem6976741 _128066 h1) (fun x'' : type642 _128066 => fun h0 : term275 _128066 x'' => @lem6980128 _128066 x'' x h0 h2 h3 h4)). Qed.
Lemma lem6980130 {_128066 A : Type'} (x : type684 _128066) (h1 : term12 _128066) (h2 : term12 A) (h3 : term38) (h4 : term10 _128066) (h5 : term384 _128066 x) : False.
Proof. exact (ex_elim (@lem6977135 A h2) (fun x' : type642 A => fun h0 : term275 A x' => @lem6980129 _128066 x h1 h3 h4 h5)). Qed.
Lemma lem6980131 {_128066 A : Type'} (h1 : term12 _128066) (h2 : term11 _128066) (h3 : term12 A) (h4 : term38) (h5 : term10 _128066) : False.
Proof. exact (ex_elim (@lem6977459 _128066 h2) (fun x : type684 _128066 => fun h0 : term386 _128066 x => @lem6980130 _128066 A x h1 h3 h4 h5 h0)). Qed.
Lemma lem6980132 {_128066 A : Type'} (h1 : term12 _128066) (h2 : term12 A) (h3 : term38) (h4 : term10 _128066) : term17 _128066.
Proof. exact (fun h0 : term11 _128066 => @lem6980131 _128066 A h1 h0 h2 h3 h4). Qed.
Lemma lem6980133 {_128066 : Type'} : (term17 _128066) = (term18 _128066).
Proof. exact (@lem69 (term11 _128066)). Qed.
Lemma lem6980134 {_128066 A : Type'} (h1 : term12 _128066) (h2 : term12 A) (h3 : term38) (h4 : term10 _128066) : term18 _128066.
Proof. exact (EQ_MP (@lem6980133 _128066) (@lem6980132 _128066 A h1 h2 h3 h4)). Qed.
Lemma lem6980135 {_128066 A : Type'} (h1 : term12 _128066) (h2 : term12 A) (h3 : term10 _128066) : term21 _128066.
Proof. exact (fun h0 : term38 => @lem6980134 _128066 A h1 h2 h0 h3). Qed.
Lemma lem6980136 {_128066 A : Type'} (h1 : term12 _128066) (h2 : term10 _128066) : term24 _128066 A.
Proof. exact (fun h0 : term12 A => @lem6980135 _128066 A h1 h0 h2). Qed.
Lemma lem6980137 {_128066 A : Type'} (h1 : term10 _128066) : term26 _128066 A.
Proof. exact (fun h0 : term12 _128066 => @lem6980136 _128066 A h0 h1). Qed.
Lemma lem6980138 {_128066 A : Type'} : term28 _128066 A.
Proof. exact (fun h0 : term10 _128066 => @lem6980137 _128066 A h0). Qed.
Lemma lem6980139 {_128066 A : Type'} : term13 _128066 A.
Proof. exact (EQ_MP (@lem6976179 _128066 A) (@lem6980138 _128066 A)). Qed.
Lemma lem6980141 {_128066 A : Type'} : term13 _128066 A.
Proof. exact (@lem6975665 _128066 A (@lem6980139 _128066 A)). Qed.
Lemma lem6980142 {_128066 A : Type'} (h1 : term10 _128066) : term25 _128066 A.
Proof. exact (@lem6980141 _128066 A (@lem6975642 _128066 h1)). Qed.
Lemma lem6980143 {_128066 A : Type'} (h1 : term10 _128066) : term23 _128066 A.
Proof. exact (@lem6980142 _128066 A h1 (@lem6975646 _128066)). Qed.
Lemma lem6980144 {_128066 : Type'} (h1 : term10 _128066) : term20 _128066.
Proof. exact (@lem6980143 _128066 Prop h1 (@lem6975627 Prop)). Qed.
Lemma lem6980145 {_128066 : Type'} (h1 : term10 _128066) : term17 _128066.
Proof. exact (@lem6980144 _128066 h1 (@lem98439)). Qed.
Lemma lem6980146 {_128066 : Type'} (h1 : term10 _128066) : False.
Proof. exact (@lem6980145 _128066 h1 (@lem6975643 _128066)). Qed.
Lemma lem6980147 {_128066 : Type'} (h1 : term10 _128066) : (term10 _128066) = False.
Proof. exact (prop_ext (fun h2 : term10 _128066 => @lem6980146 _128066 h1) (fun h2 : False => @lem6975642 _128066 h1)). Qed.
Lemma lem6980148 {_128066 : Type'} (h1 : term10 _128066) : False.
Proof. exact (EQ_MP (@lem6980147 _128066 h1) (@lem6975642 _128066 h1)). Qed.
Lemma lem6980149 {_128066 : Type'} : term9 _128066.
Proof. exact (fun h0 : term10 _128066 => @lem6980148 _128066 h0). Qed.
Lemma lem6980150 {_128066 : Type'} : term8 _128066.
Proof. exact (EQ_MP (@lem6975641 _128066) (@lem6980149 _128066)). Qed.
