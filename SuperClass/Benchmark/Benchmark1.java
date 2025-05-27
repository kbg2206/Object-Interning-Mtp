public class Benchmark1 {
    int a;
    int b;
    public Benchmark1(int x, int y) {
        a = x;
        b = y;
    }
    
    public int sum() {
        return a + b;
    }

    @Override
    public boolean equals(Object obj) {
    // Check if the object is compared with itself
    if (this == obj) {
        return true;
    }
    
    // Check if obj is an instance of Benchmark1
    if (obj == null || getClass() != obj.getClass()) {
        return false;
    }
    
    // Typecast obj to Benchmark1
    Benchmark1 other = (Benchmark1) obj;
    
    // Compare the fields
    return this.a == other.a && this.b == other.b;
}

    
    public static void main(String[] args) {

        long startTime = System.currentTimeMillis();

        Benchmark1[] benchmarkArray = new Benchmark1[100000];
        
        for(int i=0;i<100000;++i)
        {
            benchmarkArray[i] = new Benchmark1(3, 4);
        }
        
        for(int i=0;i<100000;++i)
        {
            for(int j=i+1;j<100000;++j)
            {
                if(benchmarkArray[i].equals(benchmarkArray[j]))
                {
                    // System.out.println("Objects are equal ");
                }
                else
                {
                    // System.out.println("Objects are not equal ");
                }
            }
        }
        
        
        
        long endTime = System.currentTimeMillis();
        
        System.out.println("Time taken: " + (endTime - startTime) + " ms");
    }

}
