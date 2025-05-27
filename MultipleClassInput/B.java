
public class B extends C{
    int b;
    B(int y, int z,int w)
    {
        super(z,w);
        b = y;
        System.out.println("B constructor called ");
    }
}
