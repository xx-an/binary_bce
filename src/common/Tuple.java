package common;

public class Tuple<X, Y> {
	public final X x;
	public final Y y;
	
	public Tuple(X x, Y y) { 
        this.x = x; 
        this.y = y; 
    }
	
	public X getX() {
		return this.x;
	}
	
	public Y getY() {
		return this.y;
	}
	
	@Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }

        if (obj.getClass() != this.getClass()) {
            return false;
        }
        
        @SuppressWarnings("unchecked")
		final Tuple<X, Y> other = (Tuple<X, Y>) obj;

        if ((this.x == null) ? (other.x != null) : !this.x.equals(other.x)) {
            return false;
        }

        if ((this.y == null) ? (other.y != null) : !this.y.equals(other.y)) {
            return false;
        }

        return true;
    }
	
	@Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.x != null ? this.x.hashCode() : 0);
        hash = 53 * hash + (this.y != null ? this.y.hashCode() : 0);
        return hash;
    }
	
	@Override
    public String toString() {
		String res = "(" + this.x.toString() + ", " + this.y.toString() + ")";
		return res;
    }
}
