interface Subtract<A extends Subtract> {
  Boolean leq(A y);
  void subtract(A x);
}

/*
class SubtrOver<A extends Number> implements Subtract<SubtrOver<A>> {
  A value;

  public Boolean leq(SubtrOver<A> x) {
    return value <= x.value;
  }

  public void subtract(SubtrOver<A> x) {
    value = value - x.value;
  }

}
*/

class SubtrInt implements Subtract<SubtrInt> {
  int value;

  public Boolean leq(SubtrInt x) {
    return value <= x.value;
  }

  public void subtract(SubtrInt x) {
    value = value - x.value;
  }

}

class Node<A extends Subtract<A>> {

  Node<A> parent, leftChild, rightSib;
  A value;

  Node<A> dupe() {
    Node<A> ans = new Node<A>();
    ans.value = value;
    ans.parent = parent;
    ans.leftChild = leftChild;
    ans.rightSib = rightSib;
    return ans;
  }
}



public class PairingHeap {

  static <A extends Subtract<A>> 
   Node<A> link(Node<A> x, Node<A> y) {

    if (null == x) {
      return y;
    }

    if (null == y) {
      return x;
    }

    assert (x.rightSib == null);
    assert (y.rightSib == null);
    assert (x.parent == null);
    assert (y.parent == null);
    assert (x.value != null);
    assert (y.value != null);

    Node<A> ans = x.dupe();
    Node<A> oth = y.dupe();
    if (x.value.leq(y.value)) {
      oth.rightSib = ans.leftChild;
      oth.parent = ans;
      ans.leftChild = oth;
      return ans;
    } else {
      ans.rightSib = oth.leftChild;
      ans.parent = oth;
      oth.leftChild = ans;
      return oth;
    }
  }

  static <A extends Subtract<A>> 
   Node<A> insert(A x, Node<A> y) {

    Node<A> tree = new Node<A>();
    tree.value = x;
    tree.leftChild = null;
    tree.rightSib = null;
    tree.parent = null;

    return link(tree,y);
  }
    
  static <A extends Subtract<A>> 
   void cut(Node<A> x) {
    
    if(null != x) {
      x.parent.leftChild = x.rightSib;
      x.parent = null;
      x.rightSib = null;
    }
  }

  static <A extends Subtract<A>> 
   Node<A> decreaseKey(A del, Node<A> x, Node<A> y) {

    assert (x != null);
    assert (x.value != null);

    x.value.subtract(del);
    
    if (null == x.parent) {
      assert (y == x);
      return x;
    }

    cut(x);
    return link(x,y);
  }

  static <A extends Subtract<A>> 
   Node<A> deleteMin(Node<A> x) {
    
    if (null == x) {
      return x;
    }

    Node<A> current = x.leftChild;
    Node<A> last = null;

    while (null != current) {
      current.parent = null;
      if (null == current.rightSib) {
	current.rightSib = last;
	last = current;
	current = null;
      } else {
	Node<A> other = current.rightSib;
	Node<A> next = other.rightSib;
	other.parent = null;
	other.rightSib = null;
	current.rightSib = null;
	Node<A> ans = link(current,other);
	ans.rightSib = last;
	last = ans;
	current = next;
      }
    }

    while(current != null && current.rightSib != null) {
      Node<A> other = current.rightSib;
      Node<A> next = other.rightSib;
      other.rightSib = null;
      current.rightSib = null;
      current = link(current,other);
      current.rightSib = next;
    }

    return current;
  }

}

