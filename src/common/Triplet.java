package common;

public class Triplet<X, Y, Z> {
	public final X x;
	public final Y y;
	public final Z z;
	
	public Triplet(X x, Y y, Z z) { 
        this.x = x; 
        this.y = y; 
        this.z = z;
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
		final Triplet<X, Y, Z> other = (Triplet<X, Y, Z>) obj;

        if ((this.x == null) ? (other.x != null) : !this.x.equals(other.x)) {
            return false;
        }

        if ((this.y == null) ? (other.y != null) : !this.y.equals(other.y)) {
            return false;
        }
        
        if ((this.z == null) ? (other.z != null) : !this.z.equals(other.z)) {
            return false;
        }
        
        return true;
    }
	
	@Override
    public int hashCode() {
        int hash = 3;
        hash = 53 * hash + (this.x != null ? this.x.hashCode() : 0);
        hash = 53 * hash + (this.y != null ? this.y.hashCode() : 0);
        hash = 53 * hash + (this.z != null ? this.z.hashCode() : 0);
        return hash;
    }

}
