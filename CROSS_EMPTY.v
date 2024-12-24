Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_EMPTY_term_abbrevs.
Require Import CROSS_EQ_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4326998 {_103840 _103844 : Type'} (s : _103840 -> Prop) : term0 _103840 _103844 s.
Proof. exact (@lem4326997 _103840 _103844 s). Qed.
Lemma lem4326999 {_103840 _103844 : Type'} (s : _103840 -> Prop) : (term0 _103840 _103844 s) = (term1 _103840 _103844 s).
Proof. exact (eq_refl (term0 _103840 _103844 s)). Qed.
Lemma lem4327000 {_103840 _103844 : Type'} (s : _103840 -> Prop) : term1 _103840 _103844 s.
Proof. exact (EQ_MP (@lem4326999 _103840 _103844 s) (@lem4326998 _103840 _103844 s)). Qed.
Lemma lem4327001 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : term2 _103840 _103844 s t.
Proof. exact (@lem4327000 _103840 _103844 s t). Qed.
Lemma lem4327002 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : (term2 _103840 _103844 s t) = (((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term3 _103840 _103844 s t)).
Proof. exact (eq_refl (term2 _103840 _103844 s t)). Qed.
Lemma lem4327011 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term3 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4327002 _103840 _103844 s t) (@lem4327001 _103840 _103844 s t)). Qed.
Lemma lem4327012 {_103859 A : Type'} (s : A -> Prop) (t : _103859 -> Prop) : ((@CROSS _103859 A s t) = (@EMPTY (prod A _103859))) = (term4 _103859 A s t).
Proof. exact (@lem4327011 A _103859 s t). Qed.
Lemma lem4327013 {_103859 A : Type'} (s : A -> Prop) : ((@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859))) = (term5 _103859 A s).
Proof. exact (@lem4327012 _103859 A s (@EMPTY _103859)). Qed.
Lemma lem4327019 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4327020 {_103859 : Type'} (x : _103859 -> Prop) : (x = x) = True.
Proof. exact (@lem4327019 (_103859 -> Prop) x). Qed.
Lemma lem4327021 {_103859 : Type'} : ((@EMPTY _103859) = (@EMPTY _103859)) = True.
Proof. exact (@lem4327020 _103859 (@EMPTY _103859)). Qed.
Lemma lem4327022 {A : Type'} (s : A -> Prop) : (term6 A s) = (term6 A s).
Proof. exact (eq_refl (term6 A s)). Qed.
Lemma lem4327023 {_103859 A : Type'} (s : A -> Prop) : (term5 _103859 A s) = (term7 A s).
Proof. exact (MK_COMB (@lem4327022 A s) (@lem4327021 _103859)). Qed.
Lemma lem4327025 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4327026 {A : Type'} (s : A -> Prop) : (term7 A s) = True.
Proof. exact (@lem4327025 (s = (@EMPTY A))). Qed.
Lemma lem4327027 {_103859 A : Type'} (s : A -> Prop) : (term5 _103859 A s) = True.
Proof. exact (TRANS (@lem4327023 _103859 A s) (@lem4327026 A s)). Qed.
Lemma lem4327028 {_103859 A : Type'} (s : A -> Prop) : ((@CROSS _103859 A s (@EMPTY _103859)) = (@EMPTY (prod A _103859))) = True.
Proof. exact (TRANS (@lem4327013 _103859 A s) (@lem4327027 _103859 A s)). Qed.
Lemma lem4327029 {_103859 A : Type'} : (term8 _103859 A) = (term9 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4327028 _103859 A s)). Qed.
Lemma lem4327030 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4327031 {_103859 A : Type'} : (term10 _103859 A) = (term11 A).
Proof. exact (MK_COMB (@lem4327030 A) (@lem4327029 _103859 A)). Qed.
Lemma lem4327033 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327034 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (@lem4327033 (A -> Prop) t). Qed.
Lemma lem4327035 {A : Type'} : (term11 A) = True.
Proof. exact (@lem4327034 A True). Qed.
Lemma lem4327036 {_103859 A : Type'} : (term10 _103859 A) = True.
Proof. exact (TRANS (@lem4327031 _103859 A) (@lem4327035 A)). Qed.
Lemma lem4327037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4327038 {_103859 A : Type'} : (term14 _103859 A) = (and True).
Proof. exact (MK_COMB (@lem4327037) (@lem4327036 _103859 A)). Qed.
Lemma lem4327044 {_103840 _103844 : Type'} (s : _103840 -> Prop) (t : _103844 -> Prop) : ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = (term3 _103840 _103844 s t).
Proof. exact (EQ_MP (@lem4327002 _103840 _103844 s t) (@lem4327001 _103840 _103844 s t)). Qed.
Lemma lem4327045 {_103872 B : Type'} (s : _103872 -> Prop) (t : B -> Prop) : ((@CROSS B _103872 s t) = (@EMPTY (prod _103872 B))) = (term3 _103872 B s t).
Proof. exact (@lem4327044 _103872 B s t). Qed.
Lemma lem4327046 {_103872 B : Type'} (t : B -> Prop) : ((@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B))) = (term15 _103872 B t).
Proof. exact (@lem4327045 _103872 B (@EMPTY _103872) t). Qed.
Lemma lem4327050 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4327051 {_103872 : Type'} (x : _103872 -> Prop) : (x = x) = True.
Proof. exact (@lem4327050 (_103872 -> Prop) x). Qed.
Lemma lem4327052 {_103872 : Type'} : ((@EMPTY _103872) = (@EMPTY _103872)) = True.
Proof. exact (@lem4327051 _103872 (@EMPTY _103872)). Qed.
Lemma lem4327053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4327054 {_103872 : Type'} : (term16 _103872) = (or True).
Proof. exact (MK_COMB (@lem4327053) (@lem4327052 _103872)). Qed.
Lemma lem4327057 {B : Type'} (t : B -> Prop) : (t = (@EMPTY B)) = (t = (@EMPTY B)).
Proof. exact (eq_refl (t = (@EMPTY B))). Qed.
Lemma lem4327058 {_103872 B : Type'} (t : B -> Prop) : (term15 _103872 B t) = (term17 B t).
Proof. exact (MK_COMB (@lem4327054 _103872) (@lem4327057 B t)). Qed.
Lemma lem4327060 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4327061 {B : Type'} (t : B -> Prop) : (term17 B t) = True.
Proof. exact (@lem4327060 (t = (@EMPTY B))). Qed.
Lemma lem4327062 {_103872 B : Type'} (t : B -> Prop) : (term15 _103872 B t) = True.
Proof. exact (TRANS (@lem4327058 _103872 B t) (@lem4327061 B t)). Qed.
Lemma lem4327063 {_103872 B : Type'} (t : B -> Prop) : ((@CROSS B _103872 (@EMPTY _103872) t) = (@EMPTY (prod _103872 B))) = True.
Proof. exact (TRANS (@lem4327046 _103872 B t) (@lem4327062 _103872 B t)). Qed.
Lemma lem4327064 {_103872 B : Type'} : (term18 _103872 B) = (term9 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem4327063 _103872 B t)). Qed.
Lemma lem4327065 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4327066 {_103872 B : Type'} : (term19 _103872 B) = (term11 B).
Proof. exact (MK_COMB (@lem4327065 B) (@lem4327064 _103872 B)). Qed.
Lemma lem4327068 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327069 {B : Type'} (t : Prop) : (term13 B t) = t.
Proof. exact (@lem4327068 (B -> Prop) t). Qed.
Lemma lem4327070 {B : Type'} : (term11 B) = True.
Proof. exact (@lem4327069 B True). Qed.
Lemma lem4327071 {_103872 B : Type'} : (term19 _103872 B) = True.
Proof. exact (TRANS (@lem4327066 _103872 B) (@lem4327070 B)). Qed.
Lemma lem4327072 {_103859 _103872 A B : Type'} : (term20 _103859 _103872 A B) = (True /\ True).
Proof. exact (MK_COMB (@lem4327038 _103859 A) (@lem4327071 _103872 B)). Qed.
Lemma lem4327074 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4327075 : (True /\ True) = True.
Proof. exact (@lem4327074 True). Qed.
Lemma lem4327076 {_103859 _103872 A B : Type'} : (term20 _103859 _103872 A B) = True.
Proof. exact (TRANS (@lem4327072 _103859 _103872 A B) (@lem4327075)). Qed.
Lemma lem4327077 {_103859 _103872 A B : Type'} : True = (term20 _103859 _103872 A B).
Proof. exact (SYM (@lem4327076 _103859 _103872 A B)). Qed.
Lemma lem4327078 {_103859 _103872 A B : Type'} : term20 _103859 _103872 A B.
Proof. exact (EQ_MP (@lem4327077 _103859 _103872 A B) (@lem0)). Qed.
