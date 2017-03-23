using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace dyntest
{
    namespace Kafka
    {
        class A
        {
            public A()
            {

            }
            public dynamic m(dynamic x)
            {
                return this;
            }

        }
        class I
        {
            public I()
            {

            }
            public dynamic n(dynamic x)
            {
                return this;
            }

        }
        class T
        {
            public T()
            {

            }
            public dynamic s(dynamic x)
            {
                return this;
            }

            public dynamic t(dynamic x)
            {
                return this.s(x);
            }

        }
        class Program
        {
            static void Main(string[] args)
            {
                new T().t(new A());
            }
        }
    }
}
