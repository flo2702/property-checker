package case_study;

//@ predicate AgedOver(int sAge, int age;) = sAge >= age;
//@ predicate AllowedFor(int sAgeRestriction, int age;) = sAgeRestriction <= age;
//@ predicate PossiblyEmpty(SortedList s;) = s != null;
//@ predicate NonEmpty(Node sFirst;) = sFirst != null;
//@ predicate Interval(int s, int min, int max;) = min <= s &*& s <= max;
//@ predicate NonNull(Object s;) = s != null;
//@ predicate MonotonicNonNull() = true; // inexact, but monotonicity is not expressible as a property type
//@ predicate NonNegative(int s;) = s >= 0;
//@ predicate NonPositive(int s;) = s <= 0;
//@ predicate Negative(int s;) = s < 0;
//@ predicate Positive(int s;) = s > 0;
//@ predicate Zero(int s;) = s == 0;

//@ predicate Sorted(Order sHead, Node sTail;) = sTail == null ? true : ([_](sTail.head |-> ?th) &*& [_](sTail.tail |-> ?tt) &*& SortedOrders(sHead,th) &*& Sorted(th, tt));
//@ predicate SortedOrders(Order order0, Order order1;) = OrderPred(order0, ?price0) &*& OrderPred(order1, ?price1) &*& price0 <= price1;
//@ predicate OrderPred(Order order; int price) = [_](order.product |-> ?p) &*& [_](p.price |-> price);
