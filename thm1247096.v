Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247096_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm1246844_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1246914 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1246915 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1246914 m n p h1)). Qed.
Lemma lem1246916 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1246917 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1246916 m n p h1)). Qed.
Lemma lem1246918 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1246915 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1246917 m n p h1)). Qed.
Lemma lem1246919 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1246918 m n p)). Qed.
Lemma lem1246920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246921 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1246920) (@lem1246919 m n)). Qed.
Lemma lem1246922 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1246921 m n)). Qed.
Lemma lem1246923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246924 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1246923) (@lem1246922 m)). Qed.
Lemma lem1246925 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1246924 m)). Qed.
Lemma lem1246926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246927 : term12 = term13.
Proof. exact (MK_COMB (@lem1246926) (@lem1246925)). Qed.
Lemma lem1246928 : term13.
Proof. exact (EQ_MP (@lem1246927) (@lem77960)). Qed.
Lemma lem1246929 (m : nat) : term14 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1246930 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1246931 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1246930 m) (@lem1246929 m)). Qed.
Lemma lem1246932 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1246931 m n). Qed.
Lemma lem1246933 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1246934 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1246933 m n) (@lem1246932 m n)). Qed.
Lemma lem1246935 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem1246934 m n p). Qed.
Lemma lem1246936 (m : nat) (n : nat) (p : nat) : (term18 m n p) = ((term19 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1246938 (m : nat) : term20 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1246939 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1246940 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1246939 m) (@lem1246938 m)). Qed.
Lemma lem1246941 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1246940 m n). Qed.
Lemma lem1246942 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1246943 (m : nat) (n : nat) : term23 m n.
Proof. exact (EQ_MP (@lem1246942 m n) (@lem1246941 m n)). Qed.
Lemma lem1246944 (m : nat) (n : nat) : (term23 m n) = ((term23 m n) = True).
Proof. exact (@lem7 (term23 m n)). Qed.
Lemma lem1246946 (m : nat) : term24 m.
Proof. exact (@lem1246928 m). Qed.
Lemma lem1246947 (m : nat) : (term24 m) = (term9 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1246948 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1246947 m) (@lem1246946 m)). Qed.
Lemma lem1246949 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1246948 m n). Qed.
Lemma lem1246950 (m : nat) (n : nat) : (term25 m n) = (term5 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1246951 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1246950 m n) (@lem1246949 m n)). Qed.
Lemma lem1246952 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem1246951 m n p). Qed.
Lemma lem1246953 (m : nat) (n : nat) (p : nat) : (term26 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term26 m n p)). Qed.
Lemma lem1246955 (_22840 : nat) (_22841 : nat) (n : nat) (m : nat) (p : nat) : (term27 n m p _22841 _22840) = (term28 _22840 _22841 n m p).
Proof. exact (@lem1246844 _22840 _22841 (term29 n m p)). Qed.
Lemma lem1246956 (n : nat) (m : nat) (p : nat) : (term30 p m n) = (term31 n m p).
Proof. exact (@lem1246955 n m n m p). Qed.
Lemma lem1246957 (d : nat) (n : nat) (m : nat) (p : nat) : (term32 n m p d) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (eq_refl (term32 n m p d)). Qed.
Lemma lem1246958 (n : nat) (m : nat) (d : nat) : (term34 n m d) = (term34 n m d).
Proof. exact (eq_refl (term34 n m d)). Qed.
Lemma lem1246959 (d : nat) (n : nat) (m : nat) (p : nat) : (term35 n m p d) = (term36 d n m p).
Proof. exact (MK_COMB (@lem1246958 n m d) (@lem1246957 d n m p)). Qed.
Lemma lem1246960 (d : nat) (n : nat) (m : nat) (p : nat) : (term32 n m p d) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (eq_refl (term32 n m p d)). Qed.
Lemma lem1246961 (m : nat) (n : nat) (d : nat) : (term34 m n d) = (term34 m n d).
Proof. exact (eq_refl (term34 m n d)). Qed.
Lemma lem1246962 (d : nat) (n : nat) (m : nat) (p : nat) : (term37 n m p d) = (term38 d n m p).
Proof. exact (MK_COMB (@lem1246961 m n d) (@lem1246960 d n m p)). Qed.
Lemma lem1246963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1246964 (d : nat) (n : nat) (m : nat) (p : nat) : (term39 n m p d) = (term40 d n m p).
Proof. exact (MK_COMB (@lem1246963) (@lem1246962 d n m p)). Qed.
Lemma lem1246965 (d : nat) (n : nat) (m : nat) (p : nat) : (term41 n m p d) = (term42 d n m p).
Proof. exact (MK_COMB (@lem1246964 d n m p) (@lem1246959 d n m p)). Qed.
Lemma lem1246966 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term44 n m p).
Proof. exact (fun_ext (fun d : nat => @lem1246965 d n m p)). Qed.
Lemma lem1246967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1246968 (n : nat) (m : nat) (p : nat) : (term31 n m p) = (term45 n m p).
Proof. exact (MK_COMB (@lem1246967) (@lem1246966 n m p)). Qed.
Lemma lem1246969 (n : nat) (m : nat) (p : nat) : (term30 p m n) = ((term46 m n p) = (term33 n m p)).
Proof. exact (eq_refl (term30 p m n)). Qed.
Lemma lem1246970 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1246971 (n : nat) (m : nat) (p : nat) : (term47 p m n) = (term48 n m p).
Proof. exact (MK_COMB (@lem1246970) (@lem1246969 n m p)). Qed.
Lemma lem1246972 (n : nat) (m : nat) (p : nat) : ((term30 p m n) = (term31 n m p)) = (((term46 m n p) = (term33 n m p)) = (term45 n m p)).
Proof. exact (MK_COMB (@lem1246971 n m p) (@lem1246968 n m p)). Qed.
Lemma lem1246973 (n : nat) (m : nat) (p : nat) : ((term46 m n p) = (term33 n m p)) = (term45 n m p).
Proof. exact (EQ_MP (@lem1246972 n m p) (@lem1246956 n m p)). Qed.
Lemma lem1246974 (n : nat) (m : nat) (p : nat) : (term45 n m p) = ((term46 m n p) = (term33 n m p)).
Proof. exact (SYM (@lem1246973 n m p)). Qed.
Lemma lem1246975 (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : m = (Nat.add n d).
Proof. exact (h1). Qed.
Lemma lem1246976 (d : nat) (n : nat) (p : nat) : (term49 d n p) = (term49 d n p).
Proof. exact (eq_refl (term49 d n p)). Qed.
Lemma lem1246977 (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (term50 d n p m) = (term51 p n d).
Proof. exact (MK_COMB (@lem1246976 d n p) (@lem1246975 m n d h1)). Qed.
Lemma lem1246978 (n : nat) (d : nat) (p : nat) : (term51 p n d) = ((Peano.le d p) = (term52 n d p)).
Proof. exact (eq_refl (term51 p n d)). Qed.
Lemma lem1246979 (d : nat) (n : nat) (p : nat) (m : nat) : (term53 d n p m) = (term53 d n p m).
Proof. exact (eq_refl (term53 d n p m)). Qed.
Lemma lem1246980 (m : nat) (n : nat) (d : nat) (p : nat) : ((term50 d n p m) = (term51 p n d)) = ((term50 d n p m) = ((Peano.le d p) = (term52 n d p))).
Proof. exact (MK_COMB (@lem1246979 d n p m) (@lem1246978 n d p)). Qed.
Lemma lem1246981 (d : nat) (n : nat) (m : nat) (p : nat) : (term50 d n p m) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (eq_refl (term50 d n p m)). Qed.
Lemma lem1246982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1246983 (d : nat) (n : nat) (m : nat) (p : nat) : (term53 d n p m) = (term54 d n m p).
Proof. exact (MK_COMB (@lem1246982) (@lem1246981 d n m p)). Qed.
Lemma lem1246984 (n : nat) (d : nat) (p : nat) : ((Peano.le d p) = (term52 n d p)) = ((Peano.le d p) = (term52 n d p)).
Proof. exact (eq_refl ((Peano.le d p) = (term52 n d p))). Qed.
Lemma lem1246985 (m : nat) (n : nat) (d : nat) (p : nat) : ((term50 d n p m) = ((Peano.le d p) = (term52 n d p))) = (((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term52 n d p))).
Proof. exact (MK_COMB (@lem1246983 d n m p) (@lem1246984 n d p)). Qed.
Lemma lem1246986 (m : nat) (n : nat) (d : nat) (p : nat) : ((term50 d n p m) = (term51 p n d)) = (((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term52 n d p))).
Proof. exact (TRANS (@lem1246980 m n d p) (@lem1246985 m n d p)). Qed.
Lemma lem1246987 (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term52 n d p)).
Proof. exact (EQ_MP (@lem1246986 m n d p) (@lem1246977 p m n d h1)). Qed.
Lemma lem1246988 (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : ((Peano.le d p) = (term52 n d p)) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (SYM (@lem1246987 p m n d h1)). Qed.
Lemma lem1246989 (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : n = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1246990 (d : nat) (m : nat) (p : nat) : (term55 d m p) = (term55 d m p).
Proof. exact (eq_refl (term55 d m p)). Qed.
Lemma lem1246991 (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (term56 d m p n) = (term57 p m d).
Proof. exact (MK_COMB (@lem1246990 d m p) (@lem1246989 n m d h1)). Qed.
Lemma lem1246992 (d : nat) (m : nat) (p : nat) : (term57 p m d) = ((Peano.le d p) = (term58 d m p)).
Proof. exact (eq_refl (term57 p m d)). Qed.
Lemma lem1246993 (d : nat) (m : nat) (p : nat) (n : nat) : (term59 d m p n) = (term59 d m p n).
Proof. exact (eq_refl (term59 d m p n)). Qed.
Lemma lem1246994 (n : nat) (d : nat) (m : nat) (p : nat) : ((term56 d m p n) = (term57 p m d)) = ((term56 d m p n) = ((Peano.le d p) = (term58 d m p))).
Proof. exact (MK_COMB (@lem1246993 d m p n) (@lem1246992 d m p)). Qed.
Lemma lem1246995 (d : nat) (n : nat) (m : nat) (p : nat) : (term56 d m p n) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (eq_refl (term56 d m p n)). Qed.
Lemma lem1246996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1246997 (d : nat) (n : nat) (m : nat) (p : nat) : (term59 d m p n) = (term54 d n m p).
Proof. exact (MK_COMB (@lem1246996) (@lem1246995 d n m p)). Qed.
Lemma lem1246998 (d : nat) (m : nat) (p : nat) : ((Peano.le d p) = (term58 d m p)) = ((Peano.le d p) = (term58 d m p)).
Proof. exact (eq_refl ((Peano.le d p) = (term58 d m p))). Qed.
Lemma lem1246999 (n : nat) (d : nat) (m : nat) (p : nat) : ((term56 d m p n) = ((Peano.le d p) = (term58 d m p))) = (((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term58 d m p))).
Proof. exact (MK_COMB (@lem1246997 d n m p) (@lem1246998 d m p)). Qed.
Lemma lem1247000 (n : nat) (d : nat) (m : nat) (p : nat) : ((term56 d m p n) = (term57 p m d)) = (((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term58 d m p))).
Proof. exact (TRANS (@lem1246994 n d m p) (@lem1246999 n d m p)). Qed.
Lemma lem1247001 (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((Peano.le d p) = (term33 n m p)) = ((Peano.le d p) = (term58 d m p)).
Proof. exact (EQ_MP (@lem1247000 n d m p) (@lem1246991 p n m d h1)). Qed.
Lemma lem1247002 (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : ((Peano.le d p) = (term58 d m p)) = ((Peano.le d p) = (term33 n m p)).
Proof. exact (SYM (@lem1247001 p n m d h1)). Qed.
Lemma lem1247008 (m : nat) (n : nat) (p : nat) : (term19 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1246936 m n p) (@lem1246935 m n p)). Qed.
Lemma lem1247009 (n : nat) (d : nat) (p : nat) : (term19 d n p) = (Peano.le d p).
Proof. exact (@lem1247008 n d p). Qed.
Lemma lem1247010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247011 (n : nat) (d : nat) (p : nat) : (term60 d n p) = (term61 d p).
Proof. exact (MK_COMB (@lem1247010) (@lem1247009 n d p)). Qed.
Lemma lem1247015 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1246953 m n p) (@lem1246952 m n p)). Qed.
Lemma lem1247016 (n : nat) (d : nat) (p : nat) : (term1 n d p) = (term0 n d p).
Proof. exact (@lem1247015 n d p). Qed.
Lemma lem1247017 (n : nat) : (Peano.le n) = (Peano.le n).
Proof. exact (eq_refl (Peano.le n)). Qed.
Lemma lem1247018 (n : nat) (d : nat) (p : nat) : (term62 n d p) = (term63 n d p).
Proof. exact (MK_COMB (@lem1247017 n) (@lem1247016 n d p)). Qed.
Lemma lem1247020 (m : nat) (n : nat) : (term23 m n) = True.
Proof. exact (EQ_MP (@lem1246944 m n) (@lem1246943 m n)). Qed.
Lemma lem1247021 (n : nat) (d : nat) (p : nat) : (term63 n d p) = True.
Proof. exact (@lem1247020 n (Nat.add d p)). Qed.
Lemma lem1247022 (n : nat) (d : nat) (p : nat) : (term62 n d p) = True.
Proof. exact (TRANS (@lem1247018 n d p) (@lem1247021 n d p)). Qed.
Lemma lem1247023 (n : nat) (d : nat) (p : nat) : (term52 n d p) = (term64 d p).
Proof. exact (MK_COMB (@lem1247011 n d p) (@lem1247022 n d p)). Qed.
Lemma lem1247025 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1247026 (d : nat) (p : nat) : (term64 d p) = (Peano.le d p).
Proof. exact (@lem1247025 (Peano.le d p)). Qed.
Lemma lem1247027 (n : nat) (d : nat) (p : nat) : (term52 n d p) = (Peano.le d p).
Proof. exact (TRANS (@lem1247023 n d p) (@lem1247026 d p)). Qed.
Lemma lem1247028 (d : nat) (p : nat) : (term65 d p) = (term65 d p).
Proof. exact (eq_refl (term65 d p)). Qed.
Lemma lem1247029 (n : nat) (d : nat) (p : nat) : ((Peano.le d p) = (term52 n d p)) = ((Peano.le d p) = (Peano.le d p)).
Proof. exact (MK_COMB (@lem1247028 d p) (@lem1247027 n d p)). Qed.
Lemma lem1247031 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1247032 (x : Prop) : (x = x) = True.
Proof. exact (@lem1247031 Prop x). Qed.
Lemma lem1247033 (d : nat) (p : nat) : ((Peano.le d p) = (Peano.le d p)) = True.
Proof. exact (@lem1247032 (Peano.le d p)). Qed.
Lemma lem1247034 (n : nat) (d : nat) (p : nat) : ((Peano.le d p) = (term52 n d p)) = True.
Proof. exact (TRANS (@lem1247029 n d p) (@lem1247033 d p)). Qed.
Lemma lem1247035 (n : nat) (d : nat) (p : nat) : True = ((Peano.le d p) = (term52 n d p)).
Proof. exact (SYM (@lem1247034 n d p)). Qed.
Lemma lem1247036 (n : nat) (d : nat) (p : nat) : (Peano.le d p) = (term52 n d p).
Proof. exact (EQ_MP (@lem1247035 n d p) (@lem0)). Qed.
Lemma lem1247044 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1246953 m n p) (@lem1246952 m n p)). Qed.
Lemma lem1247045 (m : nat) (d : nat) (p : nat) : (term1 m d p) = (term0 m d p).
Proof. exact (@lem1247044 m d p). Qed.
Lemma lem1247046 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem1247047 (m : nat) (d : nat) (p : nat) : (term62 m d p) = (term63 m d p).
Proof. exact (MK_COMB (@lem1247046 m) (@lem1247045 m d p)). Qed.
Lemma lem1247049 (m : nat) (n : nat) : (term23 m n) = True.
Proof. exact (EQ_MP (@lem1246944 m n) (@lem1246943 m n)). Qed.
Lemma lem1247050 (m : nat) (d : nat) (p : nat) : (term63 m d p) = True.
Proof. exact (@lem1247049 m (Nat.add d p)). Qed.
Lemma lem1247051 (m : nat) (d : nat) (p : nat) : (term62 m d p) = True.
Proof. exact (TRANS (@lem1247047 m d p) (@lem1247050 m d p)). Qed.
Lemma lem1247052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1247053 (m : nat) (d : nat) (p : nat) : (term66 m d p) = (and True).
Proof. exact (MK_COMB (@lem1247052) (@lem1247051 m d p)). Qed.
Lemma lem1247055 (m : nat) (n : nat) (p : nat) : (term19 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1246936 m n p) (@lem1246935 m n p)). Qed.
Lemma lem1247056 (m : nat) (d : nat) (p : nat) : (term19 d m p) = (Peano.le d p).
Proof. exact (@lem1247055 m d p). Qed.
Lemma lem1247057 (m : nat) (d : nat) (p : nat) : (term58 d m p) = (term67 d p).
Proof. exact (MK_COMB (@lem1247053 m d p) (@lem1247056 m d p)). Qed.
Lemma lem1247059 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1247060 (d : nat) (p : nat) : (term67 d p) = (Peano.le d p).
Proof. exact (@lem1247059 (Peano.le d p)). Qed.
Lemma lem1247061 (m : nat) (d : nat) (p : nat) : (term58 d m p) = (Peano.le d p).
Proof. exact (TRANS (@lem1247057 m d p) (@lem1247060 d p)). Qed.
Lemma lem1247062 (d : nat) (p : nat) : (term65 d p) = (term65 d p).
Proof. exact (eq_refl (term65 d p)). Qed.
Lemma lem1247063 (m : nat) (d : nat) (p : nat) : ((Peano.le d p) = (term58 d m p)) = ((Peano.le d p) = (Peano.le d p)).
Proof. exact (MK_COMB (@lem1247062 d p) (@lem1247061 m d p)). Qed.
Lemma lem1247065 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1247066 (x : Prop) : (x = x) = True.
Proof. exact (@lem1247065 Prop x). Qed.
Lemma lem1247067 (d : nat) (p : nat) : ((Peano.le d p) = (Peano.le d p)) = True.
Proof. exact (@lem1247066 (Peano.le d p)). Qed.
Lemma lem1247068 (d : nat) (m : nat) (p : nat) : ((Peano.le d p) = (term58 d m p)) = True.
Proof. exact (TRANS (@lem1247063 m d p) (@lem1247067 d p)). Qed.
Lemma lem1247069 (d : nat) (m : nat) (p : nat) : True = ((Peano.le d p) = (term58 d m p)).
Proof. exact (SYM (@lem1247068 d m p)). Qed.
Lemma lem1247070 (d : nat) (m : nat) (p : nat) : (Peano.le d p) = (term58 d m p).
Proof. exact (EQ_MP (@lem1247069 d m p) (@lem0)). Qed.
Lemma lem1247071 (p : nat) (n : nat) (m : nat) (d : nat) (h1 : n = (Nat.add m d)) : (Peano.le d p) = (term33 n m p).
Proof. exact (EQ_MP (@lem1247002 p n m d h1) (@lem1247070 d m p)). Qed.
Lemma lem1247072 (d : nat) (n : nat) (m : nat) (p : nat) : term36 d n m p.
Proof. exact (fun h0 : n = (Nat.add m d) => @lem1247071 p n m d h0). Qed.
Lemma lem1247073 (p : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add n d)) : (Peano.le d p) = (term33 n m p).
Proof. exact (EQ_MP (@lem1246988 p m n d h1) (@lem1247036 n d p)). Qed.
Lemma lem1247074 (d : nat) (n : nat) (m : nat) (p : nat) : term38 d n m p.
Proof. exact (fun h0 : m = (Nat.add n d) => @lem1247073 p m n d h0). Qed.
Lemma lem1247075 (d : nat) (n : nat) (m : nat) (p : nat) : term42 d n m p.
Proof. exact (conj (@lem1247074 d n m p) (@lem1247072 d n m p)). Qed.
Lemma lem1247080 (n : nat) (m : nat) (p : nat) : term45 n m p.
Proof. exact (fun d : nat => @lem1247075 d n m p). Qed.
Lemma lem1247081 (n : nat) (m : nat) (p : nat) : (term46 m n p) = (term33 n m p).
Proof. exact (EQ_MP (@lem1246974 n m p) (@lem1247080 n m p)). Qed.
Lemma lem1247086 (n : nat) (m : nat) : term68 n m.
Proof. exact (fun p : nat => @lem1247081 n m p). Qed.
Lemma lem1247091 (m : nat) : term69 m.
Proof. exact (fun n : nat => @lem1247086 n m). Qed.
Lemma lem1247096 : term70.
Proof. exact (fun m : nat => @lem1247091 m). Qed.
