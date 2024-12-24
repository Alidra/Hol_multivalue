Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447101_term_abbrevs.
Require Import thm0_spec.
Require Import thm11004_spec.
Require Import thm11005_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21752_spec.
Require Import thm21760_spec.
Require Import thm21772_spec.
Require Import thm21774_spec.
Lemma lem2446878 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term0 _60393 x y p) : term0 _60393 x y p.
Proof. exact (h1). Qed.
Lemma lem2446881 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term1 _60393 x y p) : term1 _60393 x y p.
Proof. exact (h1). Qed.
Lemma lem2446882 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term2 _60393 x y p.
Proof. exact (fun h0 : term1 _60393 x y p => @lem2446881 _60393 x y p h0). Qed.
Lemma lem2446883 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term2 _60393 x y p) : term2 _60393 x y p.
Proof. exact (h1). Qed.
Lemma lem2446884 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term1 _60393 x y p) : term1 _60393 x y p.
Proof. exact (h1). Qed.
Lemma lem2446885 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term1 _60393 x y p) (h2 : term2 _60393 x y p) : term1 _60393 x y p.
Proof. exact (@lem2446883 _60393 x y p h2 (@lem2446884 _60393 x y p h1)). Qed.
Lemma lem2446886 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term1 _60393 x y p) : term3 _60393 x y p.
Proof. exact (fun h0 : term2 _60393 x y p => @lem2446885 _60393 x y p h1 h0). Qed.
Lemma lem2446887 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term2 _60393 x y p) : term2 _60393 x y p.
Proof. exact (h1). Qed.
Lemma lem2446888 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term1 _60393 x y p) (h2 : term2 _60393 x y p) : term1 _60393 x y p.
Proof. exact (@lem2446886 _60393 x y p h1 (@lem2446887 _60393 x y p h2)). Qed.
Lemma lem2446889 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term2 _60393 x y p) : term2 _60393 x y p.
Proof. exact (fun h0 : term1 _60393 x y p => @lem2446888 _60393 x y p h0 h1). Qed.
Lemma lem2446890 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term4 _60393 x y p.
Proof. exact (fun h0 : term2 _60393 x y p => @lem2446889 _60393 x y p h0). Qed.
Lemma lem2446893 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term2 _60393 x y p.
Proof. exact (@lem2446890 _60393 x y p (@lem2446882 _60393 x y p)). Qed.
Lemma lem2446894 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term2 _60393 x y p.
Proof. exact (@lem2446893 _60393 x y p). Qed.
Lemma lem2446908 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2446909 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term1 _60393 x y p) = (term5 _60393 x y p).
Proof. exact (@lem2446908 (term0 _60393 x y p)). Qed.
Lemma lem2446911 (t : Prop) : (term6 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2446912 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term5 _60393 x y p) = (term7 _60393 x y p).
Proof. exact (@lem2446911 (term7 _60393 x y p)). Qed.
Lemma lem2446915 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term1 _60393 x y p) = (term7 _60393 x y p).
Proof. exact (TRANS (@lem2446909 _60393 x y p) (@lem2446912 _60393 x y p)). Qed.
Lemma lem2446920 {_60393 : Type'} (y : _60393) (p : Prop) : (term8 _60393 y p) = (term9 _60393 y p).
Proof. exact (fun_ext (fun x : _60393 => @lem2446915 _60393 x y p)). Qed.
Lemma lem2446921 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2446922 {_60393 : Type'} (y : _60393) (p : Prop) : (term10 _60393 y p) = (term11 _60393 y p).
Proof. exact (MK_COMB (@lem2446921 _60393) (@lem2446920 _60393 y p)). Qed.
Lemma lem2446927 {_60393 : Type'} (p : Prop) : (term12 _60393 p) = (term13 _60393 p).
Proof. exact (fun_ext (fun y : _60393 => @lem2446922 _60393 y p)). Qed.
Lemma lem2446928 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2446929 {_60393 : Type'} (p : Prop) : (term14 _60393 p) = (term15 _60393 p).
Proof. exact (MK_COMB (@lem2446928 _60393) (@lem2446927 _60393 p)). Qed.
Lemma lem2446934 {_60393 : Type'} : (term16 _60393) = (term17 _60393).
Proof. exact (fun_ext (fun p : Prop => @lem2446929 _60393 p)). Qed.
Lemma lem2446935 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem2446944 {_60393 : Type'} : (term18 _60393) = (term19 _60393).
Proof. exact (MK_COMB (@lem2446935) (@lem2446934 _60393)). Qed.
Lemma lem2446959 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term7 _60393 x y p) = (term7 _60393 x y p).
Proof. exact (eq_refl (term7 _60393 x y p)). Qed.
Lemma lem2446960 {_60393 : Type'} (y : _60393) (p : Prop) : (term9 _60393 y p) = (term9 _60393 y p).
Proof. exact (fun_ext (fun x : _60393 => @lem2446959 _60393 x y p)). Qed.
Lemma lem2446961 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2446962 {_60393 : Type'} (y : _60393) (p : Prop) : (term11 _60393 y p) = (term11 _60393 y p).
Proof. exact (MK_COMB (@lem2446961 _60393) (@lem2446960 _60393 y p)). Qed.
Lemma lem2446963 {_60393 : Type'} (p : Prop) : (term13 _60393 p) = (term13 _60393 p).
Proof. exact (fun_ext (fun y : _60393 => @lem2446962 _60393 y p)). Qed.
Lemma lem2446964 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2446965 {_60393 : Type'} (p : Prop) : (term15 _60393 p) = (term15 _60393 p).
Proof. exact (MK_COMB (@lem2446964 _60393) (@lem2446963 _60393 p)). Qed.
Lemma lem2446966 {_60393 : Type'} : (term17 _60393) = (term17 _60393).
Proof. exact (fun_ext (fun p : Prop => @lem2446965 _60393 p)). Qed.
Lemma lem2446967 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem2446968 {_60393 : Type'} : (term19 _60393) = (term19 _60393).
Proof. exact (MK_COMB (@lem2446967) (@lem2446966 _60393)). Qed.
Lemma lem2446969 {_60393 : Type'} : (term18 _60393) = (term19 _60393).
Proof. exact (TRANS (@lem2446944 _60393) (@lem2446968 _60393)). Qed.
Lemma lem2446975 (P : Prop -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem11005 P) (@lem11004 P)). Qed.
Lemma lem2446976 {_60393 : Type'} : (term22 _60393) = (term23 _60393).
Proof. exact (@lem2446975 (term17 _60393)). Qed.
Lemma lem2446977 {_60393 : Type'} (p : Prop) : (term24 _60393 p) = (term15 _60393 p).
Proof. exact (eq_refl (term24 _60393 p)). Qed.
Lemma lem2446978 {_60393 : Type'} : (term25 _60393) = (term17 _60393).
Proof. exact (fun_ext (fun p : Prop => @lem2446977 _60393 p)). Qed.
Lemma lem2446979 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem2446980 {_60393 : Type'} : (term22 _60393) = (term19 _60393).
Proof. exact (MK_COMB (@lem2446979) (@lem2446978 _60393)). Qed.
Lemma lem2446981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2446982 {_60393 : Type'} : (term26 _60393) = (term27 _60393).
Proof. exact (MK_COMB (@lem2446981) (@lem2446980 _60393)). Qed.
Lemma lem2446983 {_60393 : Type'} : (term28 _60393) = (term29 _60393).
Proof. exact (eq_refl (term28 _60393)). Qed.
Lemma lem2446984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2446985 {_60393 : Type'} : (term30 _60393) = (term31 _60393).
Proof. exact (MK_COMB (@lem2446984) (@lem2446983 _60393)). Qed.
Lemma lem2446986 {_60393 : Type'} : (term32 _60393) = (term33 _60393).
Proof. exact (eq_refl (term32 _60393)). Qed.
Lemma lem2446987 {_60393 : Type'} : (term23 _60393) = (term34 _60393).
Proof. exact (MK_COMB (@lem2446985 _60393) (@lem2446986 _60393)). Qed.
Lemma lem2446988 {_60393 : Type'} : ((term22 _60393) = (term23 _60393)) = ((term19 _60393) = (term34 _60393)).
Proof. exact (MK_COMB (@lem2446982 _60393) (@lem2446987 _60393)). Qed.
Lemma lem2446989 {_60393 : Type'} : (term19 _60393) = (term34 _60393).
Proof. exact (EQ_MP (@lem2446988 _60393) (@lem2446976 _60393)). Qed.
Lemma lem2447007 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem21772 t)). Qed.
Lemma lem2447008 {_60393 : Type'} (x : _60393) (y : _60393) : (term35 _60393 x y) = True.
Proof. exact (@lem2447007 (term36 _60393 x y)). Qed.
Lemma lem2447009 {_60393 : Type'} (x : _60393) (y : _60393) : (term37 _60393 x y) = (term37 _60393 x y).
Proof. exact (eq_refl (term37 _60393 x y)). Qed.
Lemma lem2447010 {_60393 : Type'} (x : _60393) (y : _60393) : (term38 _60393 x y) = (term39 _60393 x y).
Proof. exact (MK_COMB (@lem2447009 _60393 x y) (@lem2447008 _60393 x y)). Qed.
Lemma lem2447012 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem21772 t)). Qed.
Lemma lem2447013 {_60393 : Type'} (x : _60393) (y : _60393) : (term39 _60393 x y) = True.
Proof. exact (@lem2447012 (term40 _60393 x y)). Qed.
Lemma lem2447014 {_60393 : Type'} (x : _60393) (y : _60393) : (term38 _60393 x y) = True.
Proof. exact (TRANS (@lem2447010 _60393 x y) (@lem2447013 _60393 x y)). Qed.
Lemma lem2447015 {_60393 : Type'} (y : _60393) : (term41 _60393 y) = (term42 _60393).
Proof. exact (fun_ext (fun x : _60393 => @lem2447014 _60393 x y)). Qed.
Lemma lem2447016 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2447017 {_60393 : Type'} (y : _60393) : (term43 _60393 y) = (term44 _60393).
Proof. exact (MK_COMB (@lem2447016 _60393) (@lem2447015 _60393 y)). Qed.
Lemma lem2447019 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem2447020 {_60393 : Type'} (t : Prop) : (term45 _60393 t) = t.
Proof. exact (@lem2447019 _60393 t). Qed.
Lemma lem2447021 {_60393 : Type'} : (term44 _60393) = True.
Proof. exact (@lem2447020 _60393 True). Qed.
Lemma lem2447022 {_60393 : Type'} (y : _60393) : (term43 _60393 y) = True.
Proof. exact (TRANS (@lem2447017 _60393 y) (@lem2447021 _60393)). Qed.
Lemma lem2447023 {_60393 : Type'} : (term46 _60393) = (term42 _60393).
Proof. exact (fun_ext (fun y : _60393 => @lem2447022 _60393 y)). Qed.
Lemma lem2447024 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2447025 {_60393 : Type'} : (term29 _60393) = (term44 _60393).
Proof. exact (MK_COMB (@lem2447024 _60393) (@lem2447023 _60393)). Qed.
Lemma lem2447027 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem2447028 {_60393 : Type'} (t : Prop) : (term45 _60393 t) = t.
Proof. exact (@lem2447027 _60393 t). Qed.
Lemma lem2447029 {_60393 : Type'} : (term44 _60393) = True.
Proof. exact (@lem2447028 _60393 True). Qed.
Lemma lem2447030 {_60393 : Type'} : (term29 _60393) = True.
Proof. exact (TRANS (@lem2447025 _60393) (@lem2447029 _60393)). Qed.
Lemma lem2447031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2447032 {_60393 : Type'} : (term31 _60393) = (and True).
Proof. exact (MK_COMB (@lem2447031) (@lem2447030 _60393)). Qed.
Lemma lem2447048 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem21774 t)). Qed.
Lemma lem2447049 {_60393 : Type'} (x : _60393) (y : _60393) : (term47 _60393 x y) = (term48 _60393 x y).
Proof. exact (@lem2447048 (term49 _60393 x y)). Qed.
Lemma lem2447051 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem21752 t)). Qed.
Lemma lem2447052 {_60393 : Type'} (x : _60393) (y : _60393) : (term49 _60393 x y) = (x = y).
Proof. exact (@lem2447051 (x = y)). Qed.
Lemma lem2447053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2447054 {_60393 : Type'} (x : _60393) (y : _60393) : (term48 _60393 x y) = (term40 _60393 x y).
Proof. exact (MK_COMB (@lem2447053) (@lem2447052 _60393 x y)). Qed.
Lemma lem2447055 {_60393 : Type'} (x : _60393) (y : _60393) : (term47 _60393 x y) = (term40 _60393 x y).
Proof. exact (TRANS (@lem2447049 _60393 x y) (@lem2447054 _60393 x y)). Qed.
Lemma lem2447056 {_60393 : Type'} (x : _60393) (y : _60393) : (term37 _60393 x y) = (term37 _60393 x y).
Proof. exact (eq_refl (term37 _60393 x y)). Qed.
Lemma lem2447057 {_60393 : Type'} (x : _60393) (y : _60393) : (term50 _60393 x y) = (term51 _60393 x y).
Proof. exact (MK_COMB (@lem2447056 _60393 x y) (@lem2447055 _60393 x y)). Qed.
Lemma lem2447059 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem21774 t)). Qed.
Lemma lem2447060 {_60393 : Type'} (x : _60393) (y : _60393) : (term51 _60393 x y) = True.
Proof. exact (@lem2447059 (term40 _60393 x y)). Qed.
Lemma lem2447061 {_60393 : Type'} (x : _60393) (y : _60393) : (term50 _60393 x y) = True.
Proof. exact (TRANS (@lem2447057 _60393 x y) (@lem2447060 _60393 x y)). Qed.
Lemma lem2447062 {_60393 : Type'} (y : _60393) : (term52 _60393 y) = (term42 _60393).
Proof. exact (fun_ext (fun x : _60393 => @lem2447061 _60393 x y)). Qed.
Lemma lem2447063 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2447064 {_60393 : Type'} (y : _60393) : (term53 _60393 y) = (term44 _60393).
Proof. exact (MK_COMB (@lem2447063 _60393) (@lem2447062 _60393 y)). Qed.
Lemma lem2447066 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem2447067 {_60393 : Type'} (t : Prop) : (term45 _60393 t) = t.
Proof. exact (@lem2447066 _60393 t). Qed.
Lemma lem2447068 {_60393 : Type'} : (term44 _60393) = True.
Proof. exact (@lem2447067 _60393 True). Qed.
Lemma lem2447069 {_60393 : Type'} (y : _60393) : (term53 _60393 y) = True.
Proof. exact (TRANS (@lem2447064 _60393 y) (@lem2447068 _60393)). Qed.
Lemma lem2447070 {_60393 : Type'} : (term54 _60393) = (term42 _60393).
Proof. exact (fun_ext (fun y : _60393 => @lem2447069 _60393 y)). Qed.
Lemma lem2447071 {_60393 : Type'} : (@all _60393) = (@all _60393).
Proof. exact (eq_refl (@all _60393)). Qed.
Lemma lem2447072 {_60393 : Type'} : (term33 _60393) = (term44 _60393).
Proof. exact (MK_COMB (@lem2447071 _60393) (@lem2447070 _60393)). Qed.
Lemma lem2447074 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem2447075 {_60393 : Type'} (t : Prop) : (term45 _60393 t) = t.
Proof. exact (@lem2447074 _60393 t). Qed.
Lemma lem2447076 {_60393 : Type'} : (term44 _60393) = True.
Proof. exact (@lem2447075 _60393 True). Qed.
Lemma lem2447077 {_60393 : Type'} : (term33 _60393) = True.
Proof. exact (TRANS (@lem2447072 _60393) (@lem2447076 _60393)). Qed.
Lemma lem2447078 {_60393 : Type'} : (term34 _60393) = (True /\ True).
Proof. exact (MK_COMB (@lem2447032 _60393) (@lem2447077 _60393)). Qed.
Lemma lem2447080 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem21760 t)). Qed.
Lemma lem2447081 : (True /\ True) = True.
Proof. exact (@lem2447080 True). Qed.
Lemma lem2447082 {_60393 : Type'} : (term34 _60393) = True.
Proof. exact (TRANS (@lem2447078 _60393) (@lem2447081)). Qed.
Lemma lem2447083 {_60393 : Type'} : (term19 _60393) = True.
Proof. exact (TRANS (@lem2446989 _60393) (@lem2447082 _60393)). Qed.
Lemma lem2447084 {_60393 : Type'} : (term18 _60393) = True.
Proof. exact (TRANS (@lem2446969 _60393) (@lem2447083 _60393)). Qed.
Lemma lem2447085 {_60393 : Type'} : True = (term18 _60393).
Proof. exact (SYM (@lem2447084 _60393)). Qed.
Lemma lem2447086 {_60393 : Type'} : term18 _60393.
Proof. exact (EQ_MP (@lem2447085 _60393) (@lem0)). Qed.
Lemma lem2447087 {_60393 : Type'} (p : Prop) : term55 _60393 p.
Proof. exact (@lem2447086 _60393 p). Qed.
Lemma lem2447088 {_60393 : Type'} (p : Prop) : (term55 _60393 p) = (term14 _60393 p).
Proof. exact (eq_refl (term55 _60393 p)). Qed.
Lemma lem2447089 {_60393 : Type'} (p : Prop) : term14 _60393 p.
Proof. exact (EQ_MP (@lem2447088 _60393 p) (@lem2447087 _60393 p)). Qed.
Lemma lem2447090 {_60393 : Type'} (p : Prop) (y : _60393) : term56 _60393 p y.
Proof. exact (@lem2447089 _60393 p y). Qed.
Lemma lem2447091 {_60393 : Type'} (y : _60393) (p : Prop) : (term56 _60393 p y) = (term10 _60393 y p).
Proof. exact (eq_refl (term56 _60393 p y)). Qed.
Lemma lem2447092 {_60393 : Type'} (y : _60393) (p : Prop) : term10 _60393 y p.
Proof. exact (EQ_MP (@lem2447091 _60393 y p) (@lem2447090 _60393 p y)). Qed.
Lemma lem2447093 {_60393 : Type'} (y : _60393) (p : Prop) (x : _60393) : term57 _60393 y p x.
Proof. exact (@lem2447092 _60393 y p x). Qed.
Lemma lem2447094 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : (term57 _60393 y p x) = (term1 _60393 x y p).
Proof. exact (eq_refl (term57 _60393 y p x)). Qed.
Lemma lem2447095 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term1 _60393 x y p.
Proof. exact (EQ_MP (@lem2447094 _60393 x y p) (@lem2447093 _60393 y p x)). Qed.
Lemma lem2447097 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term1 _60393 x y p.
Proof. exact (@lem2446894 _60393 x y p (@lem2447095 _60393 x y p)). Qed.
Lemma lem2447098 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term0 _60393 x y p) : False.
Proof. exact (@lem2447097 _60393 x y p (@lem2446878 _60393 x y p h1)). Qed.
Lemma lem2447099 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term0 _60393 x y p) : (term0 _60393 x y p) = False.
Proof. exact (prop_ext (fun h2 : term0 _60393 x y p => @lem2447098 _60393 x y p h1) (fun h2 : False => @lem2446878 _60393 x y p h1)). Qed.
Lemma lem2447100 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) (h1 : term0 _60393 x y p) : False.
Proof. exact (EQ_MP (@lem2447099 _60393 x y p h1) (@lem2446878 _60393 x y p h1)). Qed.
Lemma lem2447101 {_60393 : Type'} (x : _60393) (y : _60393) (p : Prop) : term1 _60393 x y p.
Proof. exact (fun h0 : term0 _60393 x y p => @lem2447100 _60393 x y p h0). Qed.
