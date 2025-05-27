import java.util.Objects;



public class Example1 {
	int a ;
	int c;
	String b;

    Example1()
    {
        a = 10;
        c =9;
        b = "Hello World";
    }

    Example1(int x,int z,String y)
    {
        a = x;
        b = y;
        c = z-1;
    }
	public static void main(String[] args) {
		
        int x = 10;
        Example1 obj1 = new Example1();
        Example1 obj2 = new Example1(x,10, "Hello World");
        // Example1 obj3 = new Example1(10,"Hello");

        if(obj1.equals(obj2))
        {
            System.out.println("Objects are equal");
        }
        else
        {
            System.out.println("Objects are not equal");
        }
    }
}
